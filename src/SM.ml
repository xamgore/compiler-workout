open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter
   Takes a configuration and a program, and returns a configuration as a result
 *)
let eval (conf : config) (instructions : insn list) : config =
  let evalInsn (conf : config) (i : insn) : config =
    match i with
      | READ ->
        let (st, (mem, z :: i, o)) = conf in
          (z :: st, (mem, i, o))
      | WRITE ->
        let (z :: st, (mem, i, o)) = conf in
          (st, (mem, i, o @ [z]))
      | LD var ->
        let (st, (mem, i, o)) = conf in
          ((mem var) :: st, (mem, i, o))
      | ST var ->
        let (z :: st, (mem, i, o)) = conf in
          (st, (Language.Expr.update var z mem, i, o))
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
  in List.fold_left evalInsn conf instructions

  (* Top-level evaluation
     Takes an input stream, a program, and returns an output stream this program calculates
  *)
let run (p : insn list) (i : int list) : int list =
  let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

let rec compile (stmt : Language.Stmt.t) : insn list =
  let rec compileExpr (e : Language.Expr.t) : insn list =
    match e with
    | Language.Expr.Const (value : int) -> [CONST value]
    | Language.Expr.Var (name : string) -> [LD name]
    | Language.Expr.Binop (op, l, r)    -> (compileExpr l) @ (compileExpr r) @ [BINOP op]
  in
  match stmt with
  | Language.Stmt.Read (var: string) -> [READ; ST var]
  | Language.Stmt.Write expr         -> (compileExpr expr) @ [WRITE]
  | Language.Stmt.Assign (var, expr) -> (compileExpr expr) @ [ST var]
  | Language.Stmt.Seq (fst, snd)     -> (compile fst) @ (compile snd)
