/-
  Work Package A2

  Based on section 3
-/

/--
  Types of identifiers
-/
abbrev Label := String
abbrev Var := String

inductive RVal : Type where
  | bool: Bool → RVal

/--
  Enum of allowed operations in Rust
-/
inductive ROp where
  | add
  | sub
  | mul
-- Expand on demand

/--
  Type of Rust statements
-/
inductive RExp where
  | v     : RVal   → RExp
  | x     : Var   → RExp
  | not   : RExp → RExp
  | op    : RExp → ROp → RExp → RExp
  -- | Block
  | ife   : RExp → RExp → RExp → RExp
  | loop  : Label → RExp
  | panic : RExp
  | arr   : Array RExp → RExp

/--
  Type of Rust statements
-/
inductive RStmt where
  | mk  : RExp → RStmt 
  | lt  : Var → RVal → RStmt

/--
  Function definition in Rust

  Example:
    func "Hello World" [] RExp.v 2
-/
structure RFunc where
  func :: 
  iden : Label
  par  : List Var
  exp  : RExp

-- Program definition
structure RProg where
  prog :: 
  foo  : List RFunc
  main : RFunc

