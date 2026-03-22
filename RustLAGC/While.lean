-- This file demos the formalisation of WHILE in a LAGC semantic

-- Based on Din et al., 2024
import Std

section ExampleWhile

-- Identifier 
abbrev Name := String

inductive Exp where
  | exp : Exp
deriving Repr

inductive While where
  | skip   : While
  | assign : Name → Exp → While
  | ife    : Exp → While → While
  | conc   : While → While → While
  | while  : Exp → While → While
deriving Repr

open While
open Exp

#eval skip
#eval assign "x" exp

end ExampleWhile
