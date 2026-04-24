-- Formalisation of Rust syntax
-- Based on Drdot, 2026

-- Placeholder types
opaque Val : Type
opaque Label : Type
opaque Var : Type

inductive RExp where
  -- TODO: Splitting syntax between inductives causes boilerplate
  -- But does not restrict properly
  -- RExp
  | v     : Val   → RExp
  | x     : Var   → RExp
  | not   : RExp → RExp
  | eq    : Var   → RExp → RExp
  -- Block
  | ife   : RExp → RExp → RExp → RExp
  | loop  : Label → RExp
  | panic : RExp
  -- RExp
  | lt  : Var → Val → RExp

inductive ROp where
  | add
  | sub
  | mul
-- Expand on demand

-- Struct und Tuple sind recht ähnlich, eins sollte drin sein

-- Function definition
structure RFunc where
  iden : Label
  par  : List Var
  exp  : RExp

-- Program definition
structure RProg where
  foo  : List RFunc
  main : RFunc -- War mal RExp

