-- Formalisation of Rust syntax
-- Based on Drdot, 2026

opaque Val : Type
opaque Var : Type

inductive RExp where
  -- RExp
  | v   : Val → RExp
  | not : RExp → RExp
  -- RStmt
  | lt  : Var → Val → RExp

inductive ROp where
  | add
  | sub
  | mul
-- Expand on demand

