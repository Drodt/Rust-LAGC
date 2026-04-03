-- Formalisation of LAGC structures and functions
-- Based on Drdot, 2026

import Std
import Lean.Data.AssocList
import Mathlib.Data.Set.Basic

open Std
open Lean

-- Variables are simply of type String
abbrev Var : Type := String

-- Starred values + additional data types
inductive Place where
  | v  : Var → Place
  | pN : Nat → Place
  -- | pI : Var → Place
deriving instance BEq, Repr for Place

inductive BId where
  | bId : Var → BId
deriving instance BEq, Repr for BId

inductive SVal where
  | sym -- Equivalent to *
  | B    : Bool  → SVal -- Mapping Lean values directly to SVal
  | Z    : Int   → SVal
  | RefS : Place → BId → SVal -- Shared
  | RefM : Place → BId → SVal -- Mutable
  -- | Tup
  -- | Arr
  -- | Struct 
  -- | Enum
  -- | Func : Var → SVal -- Function
  deriving instance BEq, Repr for SVal

open SVal

-- Symbolic state
-- TODO: Changed used data structure?
abbrev State := List (Var × SVal)

-- State update
def σ_u (s : State) (u : Var × SVal) : SVal := sorry

-- Symbolic variables
def symb (σ : State) : List Var := (σ.filter (fun p => p.snd == sym)).map (fun c => c.fst)

#eval symb [("x", sym), ("y", B true)]

-- Symbolic traces
inductive EvMarker where
  | ev

-- Symbolic trace - Definition 2.1
inductive SymTrace where
  | ε : SymTrace
  | t : SVal → SymTrace

-- Well-Formed and Shining Trace - Definition 2.2
-- Definitions for use in proofs
-- def varSym
-- def evSym
-- def exten
