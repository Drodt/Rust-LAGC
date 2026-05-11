/-
  Work Package A2

  Based on section 3
-/

-- Placeholder types
abbrev RVal := String
opaque Label : Type
opaque Var : Type

inductive ROp where
  | add
  | sub
  | mul
-- Expand on demand

/--
  Type of Rust statements

  Rust expresssions are a subset of statements, preventing boiler plate constructors
-/
inductive RStmt where
  -- RExp
  | v     : RVal   → RStmt
  | x     : Var   → RStmt
  | not   : RStmt → RStmt
  | eq    : Var   → RStmt → RStmt
  | op    : RStmt → ROp → RStmt → RStmt
  -- | Block
  | ife   : RStmt → RStmt → RStmt → RStmt
  | loop  : Label → RStmt
  | panic : RStmt
  | arr   : Array RStmt → RStmt
  -- RStmt
  | lt  : Var → RVal → RStmt

-- Struct und Tuple sind recht ähnlich, eins sollte drin sein

-- Function definition
structure RFunc where
  iden : Label
  par  : List Var
  exp  : RStmt

-- Program definition
structure RProg where
  foo  : List RFunc
  main : RFunc -- War mal RStmt

