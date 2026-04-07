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

-- Self explanatory
inductive Place where
  | pV : Var → Place
  | pN : Nat → Place

deriving instance BEq, Repr for Place

-- Burrow Identifier
inductive BId where
  | bId : Var → BId
deriving instance BEq, Repr for BId

inductive SVal where
  | sym    : SVal  -- Equivalent to *
  | b      : Bool  → SVal -- Mapping Lean values directly to SVal
  | z      : Int   → SVal
  | refS   : Place → BId → SVal -- Shared reference
  | refM   : Place → BId → SVal -- Mutable reference
  | tuple  : List SVal → SVal
  -- | Arr
  | struct : Var × List (Place × SVal) → SVal -- Implied by rule 33
  -- | Enum
  -- | Func : List Var → SVal → SVaL -- Function
deriving instance BEq, Repr for SVal

open SVal

-- Symbolic state
-- TODO: Change data structure?
abbrev SymState := AssocList Var SVal

-- State update
def update (σ : SymState) (u : Var × SVal) : SymState := match σ with
  | .nil       => σ.insert u.fst u.snd
  | .cons x y xys  => if x == u.fst then σ.replace u.fst u.snd else .cons x y (update xys u)

-- Symbolic variables of a state
def symb (σ : SymState) : List Var := (σ.toList.filter (fun p => p.snd == sym)).map (fun c => c.fst)

#eval (update [].toAssocList' ("x", z 2)).toList
#eval (update [("z", sym), ("x", z 2)].toAssocList' ("z", z 2)).toList
#eval symb [("x", sym), ("y", b true)].toAssocList'

/-
  Traces and Evensts
-/

inductive EvMarker where
  | evVar : Var → EvMarker
  | evVal   : SVal → EvMarker
  | evState : SymState → EvMarker
  | ev      : List EvMarker → EvMarker

inductive Trace where
  | e : Trace
  | s : SymState → Trace

-- Symbolic traces

-- Symbolic trace - Definition 2.1
inductive SymTrace where
  | ε : SymTrace
  | t : SVal → SymTrace

-- Well-Formed and Shining Trace - Definition 2.2
-- TODO: Definitions for use in proofs?
-- def varSym
-- def evSym
-- def exten
