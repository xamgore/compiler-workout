(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators
       
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update (name : string) (value : int) (get : state) : state
      = fun y -> if name = y then value else get y


    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let rec eval (state : state) (expr : t) : int =
      let to_int  b = if b      then 1     else 0    in
      let to_bool i = if i == 0 then false else true in
        match expr with
        | Const (x)          -> x
        | Var (str)          -> state str
        | Binop ("+", x, y)  -> (eval state x) + (eval state y)
        | Binop ("-", x, y)  -> (eval state x) - (eval state y)
        | Binop ("*", x, y)  -> (eval state x) * (eval state y)
        | Binop ("/", x, y)  -> (eval state x) / (eval state y)
        | Binop ("%", x, y)  -> (eval state x) mod (eval state y)
        | Binop ("==", x, y) -> to_int (eval state x == eval state y)
        | Binop ("!=", x, y) -> to_int (eval state x != eval state y)
        | Binop ("<=", x, y) -> to_int (eval state x <= eval state y)
        | Binop (">=", x, y) -> to_int (eval state x >= eval state y)
        | Binop ("<", x, y)  -> to_int (eval state x < eval state y)
        | Binop (">", x, y)  -> to_int (eval state x > eval state y)
        | Binop ("!!", x, y) -> to_int ((to_bool (eval state x)) || (to_bool (eval state y)))
        | Binop ("&&", x, y) -> to_int ((to_bool (eval state x)) && (to_bool (eval state y)))
        | _                  -> failwith (Printf.sprintf "Unknown type of expression, can't eval")

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (
      expr: !(Util.expr
        (fun x -> x) [|
          `Lefta, [
             ostap ("!!"), (fun l r -> Binop ("!!", l, r));
           ];
          `Lefta, [
             ostap ("&&"), (fun l r -> Binop ("&&", l, r));
          ];
          `Nona,  [
             ostap (">="), (fun l r -> Binop (">=", l, r));
             ostap ("<="), (fun l r -> Binop ("<=", l, r));
             ostap (">"),  (fun l r -> Binop (">",  l, r));
             ostap ("<"),  (fun l r -> Binop ("<",  l, r));
             ostap ("=="), (fun l r -> Binop ("==", l, r));
             ostap ("!="), (fun l r -> Binop ("!=", l, r));
          ];
          `Lefta, [
            ostap ("+"), (fun l r -> Binop ("+",  l, r));
            ostap ("-"), (fun l r -> Binop ("-",  l, r));
          ];
          `Lefta, [
            ostap ("*"), (fun l r -> Binop ("*",  l, r));
            ostap ("/"), (fun l r -> Binop ("/",  l, r));
            ostap ("%"), (fun l r -> Binop ("%",  l, r));
          ];
        |]
        parse
      );
       parse: -"(" expr -")"
           | value:DECIMAL { Const value }
           | id:IDENT      { Var id }
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
    (* loop with a post-condition       *) (* add yourself *)  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (conf : config) (stmt : t) : config =
      match stmt with
       | Read var   ->
         let (mem, value :: i, o) = conf in
          (Expr.update var value mem, i, o)
       | Write expr ->
         let (mem, i, o) = conf in
          (mem, i, o @ [Expr.eval mem expr])
       | Assign (var, expr) ->
         let (mem, i, o) = conf in
          (Expr.update var (Expr.eval mem expr) mem, i, o)
       | Seq (stmt1, stmt2) ->
         let conf' = eval conf stmt1 in
          eval conf' stmt2
                               
    (* Statement parser *)
    ostap (
      read:   -"read" -"(" id: IDENT -")"           { Read id };
      write:  -"write" -"(" expr:!(Expr.expr) -")"  { Write expr };
      assign: id:IDENT -":=" expr:!(Expr.expr)      { Assign (id, expr) };
      parse:  <s::ss> : !(Util.listBy) [ostap (-";")]
                [ostap (read | write | assign)]
                { List.fold_left (fun fst snd -> Seq (fst, snd)) s ss }
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
