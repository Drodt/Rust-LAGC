-- Encode syntax of simplified rust
inductive Exp where
  | var 
  | id 
  | not 
  | op 
  | eq
  | block
  | ifElse : Exp -> Exp -> Exp

inductive Stmt where
  | exp
  | assign

structure SymTrace

def val (exp : Exp) : SymTrace
