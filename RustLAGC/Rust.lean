-- Formalisation of Rust syntax
-- Based on Drdot, 2026

-- Placeholder values
opaque Val : Type
opaque Var : Type
opaque Label : Type

inductive RStmt where
  -- TODO: Splitting syntax between inductives causes boilerplate
  -- But does not restrict properly
  -- RExp
  | v     : Val   → RStmt
  | not   : RStmt → RStmt
  | eq    : Var   → RStmt → RStmt
  -- Block
  | ife   : RStmt → RStmt → RStmt → RStmt
  | loop  : Label → RStmt
  | panic : RStmt
  -- RStmt
  | lt  : Var → Val → RStmt

structure RFunc where
  iden : Label
  par  : List Var
  exp  : RStmt

structure RProg where
  foo : List RFunc

inductive ROp where
  | add
  | sub
  | mul
-- Expand on demand

