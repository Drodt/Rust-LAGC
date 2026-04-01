-- Formalisation of LAGC structures and functions
-- Based on Drdot, 2026

import Std
import Mathlib.Data.Set.Basic

-- Variables are simply of type String
abbrev Var : Type := String

-- Symbolic values
inductive SVal where
  | sym             -- Equivalent to *
  | B : Bool → SVal -- Mapping Lean values directly to SVal
  | Z : Int  → SVal
  -- | RefS
  -- | RefM
  -- | Tup
  -- | Arr
  -- | Struct 
  -- | Enum

inductive Place where
  | v  : Var → Place
  | pN : Nat → Place
  | pI

abbrev SymState := List (Var × SVal)

inductive EvMarker where
  | ev

inductive SymTrace where
  | ε : SymTrace
  | t : SVal → EvMarker → SymTrace

open Std

def σ (x : List Var) (s : SymState) (u : SymState := List.nil): List SVal := match x with
  | _       => []
