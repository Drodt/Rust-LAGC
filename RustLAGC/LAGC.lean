-- Formalisation of LAGC structures and functions
-- Based on Drdot, 2026

import Std
import Mathlib.Data.Set.Basic

-- Variables are simply of type String
abbrev Var : Type := String

-- Starred values + additional data types
inductive Place where
  | v  : Var → Place
  | pN : Nat → Place
  -- | pI : Var → Place
deriving Repr

inductive BId where
  | bId : Var → BId
deriving Repr

inductive SVal where
  | sym                       -- Equivalent to *
  | B    : Bool  → SVal       -- Mapping Lean values directly to SVal
  | Z    : Int   → SVal
  | RefS : Place → BId → SVal -- Shared
  | RefM : Place → BId → SVal -- Mutable
  -- | Tup
  -- | Arr
  -- | Struct 
  -- | Enum
deriving Repr

-- Symbolic state
abbrev σ := List (Var × SVal)

-- Symbolic traces
inductive EvMarker where
  | ev

inductive SymTrace where
  | ε : SymTrace
  | t : SVal → EvMarker → SymTrace

open Std

