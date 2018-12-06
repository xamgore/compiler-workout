open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config


let evalInsn (conf : int list * Stmt.config) (i : insn) : (int list * Stmt.config) =
  match i with
    | READ ->
      let (st, (mem, z :: i, o)) = conf in
        (z :: st, (mem, i, o))
    | WRITE ->
      let (z :: st, (mem, i, o)) = conf in
        (st, (mem, i, o @ [z]))
    | LD var ->
      let (st, (mem, i, o)) = conf in
        (State.eval mem var :: st, (mem, i, o))
    | ST var ->
      let (z :: st, (mem, i, o)) = conf in
        (st, (Language.State.update var z mem, i, o))
    | CONST value ->
      let (st, c) = conf in
        (value :: st, c)
    | BINOP op ->
      let (y :: x :: st, c) = conf in
      let to_int  b = if b      then 1     else 0    in
      let to_bool i = if i == 0 then false else true in
      let result = match op with
        | "+" -> x + y
        | "-" -> x - y
        | "*" -> x * y
        | "/" -> x / y
        | "%" -> x mod y
        | "==" -> to_int (x == y)
        | "!=" -> to_int (x != y)
        | "<=" -> to_int (x <= y)
        | ">=" -> to_int (x >= y)
        | "<" -> to_int (x < y)
        | ">" -> to_int (x > y)
        | "!!" -> to_int ((to_bool (x)) || (to_bool (y)))
        | "&&" -> to_int ((to_bool (x)) && (to_bool (y)))
        | _ -> failwith (Printf.sprintf "Unknown type of expression, can't eval")
        in (result :: st, c)

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env (conf : config) (instructions : insn list) : config =
  match instructions with
  | [] -> conf
  | i :: intrs ->
    match i with
    | LABEL _ ->
      eval env conf intrs

    | JMP label ->
      eval env conf (env#labeled label)

    | CJMP (clause, label) ->
      let (controlStack, z :: st, state) = conf in
      let isTruth = (z = 0 && clause = "z") || (z != 0 && clause = "nz") in
      let branch = if isTruth then env#labeled label else intrs in
        eval env (controlStack, st, state) branch

    | _ ->
      let (controlStack, st, state) = conf in
      let (st', state') = evalInsn (st, state) i in
        eval env (controlStack, st', state') intrs

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o



(* counter is used to generate fresh labels,
   instead of the state monad or extra argument in the compile func *)
let counter = object
  val mutable cnt = 0
  method freshLabel = cnt <- cnt + 1; Printf.sprintf "label%d" cnt
end

let rec compileExpr (e : Language.Expr.t) : insn list =
  match e with
  | Language.Expr.Const (value : int) -> [CONST value]
  | Language.Expr.Var (name : string) -> [LD name]
  | Language.Expr.Binop (op, l, r)    -> (compileExpr l) @ (compileExpr r) @ [BINOP op]

let rec compileStmt (stmt : Language.Stmt.t) : insn list =
  match stmt with
  | Language.Stmt.Read (var: string) -> [READ; ST var]
  | Language.Stmt.Write expr         -> (compileExpr expr) @ [WRITE]
  | Language.Stmt.Assign (var, expr) -> (compileExpr expr) @ [ST var]
  | Language.Stmt.Seq (fst, snd)     -> (compileStmt fst) @ (compileStmt snd)
  | Language.Stmt.Skip               -> []
  | Language.Stmt.Repeat (body, clause) ->
    let l = counter#freshLabel in
      [LABEL l] @ (compileStmt body) @ (compileExpr clause) @ [CJMP ("z", l)]
  | Language.Stmt.While (clause, body)   ->
    let (l, lEnd) = (counter#freshLabel, counter#freshLabel) in
      [LABEL l] @ (compileExpr clause) @ [CJMP ("z", lEnd)]
                @ (compileStmt body)       @ [JMP l; LABEL lEnd]
  | Language.Stmt.If (clause, thenBr, elseBr) ->
    let (lElse, lEnd) = (counter#freshLabel, counter#freshLabel) in
      (compileExpr clause) @ [CJMP ("z", lElse)] @ (compileStmt thenBr) @ [JMP lEnd]
                           @ [LABEL lElse] @ (compileStmt elseBr) @ [LABEL lEnd]

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile _ = failwith "Not Implemented Yet"
