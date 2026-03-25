-- Implementation of LAGC structures
-- Based on Drdot, 2026

import Std

abbrev Var := String

inductive Val where
  | tt
  | ff

inductive SValues where
  | n : Nat → SValues
  | z : Int → SValues

abbrev SymState := List Var × SValues

inductive SymTrace where
  | ε : SymTrace

open Std

