-- Implementation of LAGC structures
-- Based on Drdot, 2026

import Std
import Mathlib.Data.Set.Basic

abbrev Var := String

inductive Val where
  | tt : Val
  | ff : Val

inductive SValues where
  | n : Nat → SValues
  | z : Int → SValues

abbrev SymState := List Var × SValues

inductive SymTrace where
  | ε : SymTrace

open Std

