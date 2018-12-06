(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update name value state =
      let u name value state = fun y -> if name = y then value else state y in
      if List.mem name state.scope
        then {state with l = u name value state.l}
        else {state with g = u name value state.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env (conf : config) (stmt : t) : config =
      match stmt with
       | Read var   ->
         let (mem, value :: i, o) = conf in
          (State.update var value mem, i, o)
       | Write expr ->
         let (mem, i, o) = conf in
          (mem, i, o @ [Expr.eval mem expr])
       | Assign (var, expr) ->
         let (mem, i, o) = conf in
          (State.update var (Expr.eval mem expr) mem, i, o)
       | Seq (stmt1, stmt2) ->
         let conf' = eval env conf stmt1 in
          eval env conf' stmt2
       | If (clause, thenBr, elseBr) ->
         let (mem, i, o) = conf in
         let branch = if (Expr.eval mem clause) == 0 then elseBr else thenBr in
          eval env conf branch
       | (While (clause, body)) as loop ->
         let (mem, i, o) = conf in
         if (Expr.eval mem clause) == 0 then conf else eval env (eval env conf body) loop
       (* repeat === body; while (clause) body; *)
       | (Repeat (body, clause)) ->
         let afterOneStep = eval env conf body in
         let whileClause  = Expr.Binop ("==", clause, Const 0) in
         eval env afterOneStep (While (whileClause, body))
       | Skip -> conf
       | Call (funcName, actualArgsNotNormalized) ->
         let (mem, i, o) = conf in
         let (formalArgs, localVars, body) = env#definition funcName in
         let funcScope  = State.push_scope mem (formalArgs @ localVars) in
         let actualArgs = List.map (Expr.eval mem) actualArgsNotNormalized in
         let funcScopeWithArgs = List.fold_left 
                                 (fun state (name, value) -> State.update name value state)
                                 funcScope (List.combine formalArgs actualArgs) in
         let (mem', i', o') = eval env (funcScopeWithArgs, i, o) body in
           (State.drop_scope mem' mem, i', o')

                                
    (* Statement parser *)
    ostap (                                      
      skip:   -"skip"                               { Skip };
      read:   -"read" -"(" id: IDENT -")"           { Read id };
      write:  -"write" -"(" expr:!(Expr.parse) -")" { Write expr };
      assign: id:IDENT -":=" expr:!(Expr.parse)     { Assign (id, expr) };

      whileLoop: -"while" clause:!(Expr.parse) -"do" body:parse -"od"
                                                    { While (clause, body) };

      repeatLoop: -"repeat" body:parse -"until" clause:!(Expr.parse)
                                                    { Repeat (body, clause) };

      forLoop: -"for" init:parse -"," clause:!(Expr.parse) -"," step:parse 
               -"do" body:parse -"od"               { Seq (init, While (clause, Seq (body, step))) };

      ifThen: -"if" clause:!(Expr.parse) -"then" thenBr:parse                   -"fi"
                                                    { If (clause, thenBr, Skip) }
            | -"if" clause:!(Expr.parse) -"then" thenBr:parse elseBr:elseBranch -"fi"
                                                    { If (clause, thenBr, elseBr) };
      elseBranch: -"else" body:parse { body }
                | -"elif" clause:!(Expr.parse) -"then" thenBr:parse elseBr:elseBranch
                                                    { If (clause, thenBr, elseBr) };

      funcCall: funcName:IDENT -"(" args:!(Expr.parse)* -")"
                                                    { Call (funcName, args) };

      parse:  <s::ss> : !(Util.listBy) [ostap (-";")]
                [ostap (skip | read | write | assign | whileLoop | repeatLoop | forLoop | ifThen | funcCall)]
                { List.fold_left (fun fst snd -> Seq (fst, snd)) s ss }
    )
      
  end


let fromOption o default = match o with
  | None   -> default
  | Some x -> x

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (                                      
      parse: -"fun" funcName:IDENT
             -"(" argNames:IDENT* -")"
             localVars:!( ostap ( -"local" IDENT+ ) )?
             -"{" body:!(Stmt.parse) -"}"
             { (funcName, (argNames, fromOption localVars [], body)) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
