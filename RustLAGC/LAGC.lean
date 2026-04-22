-- Formalisation of LAGC structures and functions
-- Based on Drdot, 2026

import Std
import Lean.Data.AssocList
import Mathlib.Data.Set.Basic

open Std
open Lean

-- Starred values + additional data types

/--
  Variables are simply Strings
-/
abbrev Var : Type := String

/--
  TODO
-/
inductive Place where
  | pV : Var → Place
  | pN : Nat → Place
deriving instance BEq, Repr for Place

/--
  Burrow Identifier
  TODO
-/
inductive BId where
  | bId : Var → BId
deriving instance BEq, Repr for BId

/--
  Starred values
-/
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

/--
  Symbolic state
  TODO: Change data structure?
-/
abbrev SymState :=
  AssocList Var SVal

-- State update
-- TODO: Consider cases with arrays, tuples, strcuts, enums (p.2)
def update (σ : SymState) (u : Var × SVal) : SymState := match σ with
  | .nil       => σ.insert u.fst u.snd
  | .cons x y xys  => if x == u.fst then σ.replace u.fst u.snd else .cons x y (update xys u)

/--
  Symbolic variables of a state
-/
def symb (σ : SymState) : List Var :=
  (σ.toList.filter (fun p => p.snd == sym)).map (fun c => c.fst)

#eval (update [].toAssocList' ("x", z 2)).toList
#eval (update [("z", sym), ("x", z 2)].toAssocList' ("z", z 2)).toList
#eval symb [("x", sym), ("y", b true)].toAssocList'

-- Traces and Events

-- Event markers, assuming event parameter location is irrelevant
structure EvMarker where
  ev  ::
  var : List Var
  val : List SVal -- TODO: Exclude sym

-- Symbolic trace - Definition 2.1
inductive SymTrace where
  | ε    : SymTrace
  | tS   : SymTrace → SymState → SymTrace -- Splitting the construction of trace may be sensible (also a bit of a constraint)
  | tE   : SymTrace → EvMarker → SymTrace

open SymTrace
open EvMarker

-- Empty trace
#check ε

-- Trace with state
-- TODO: Create shortcut for singleton trace
#check tS ε [("x", sym), ("y", b true)].toAssocList'

-- Trace with event
#check tE ε $ ev [] []

#check (ε.tS [("x",sym)].toAssocList').tE $ ev [] []

def concat (a b : SymTrace) : SymTrace := sorry

def chop (a b : SymTrace) : SymTrace := sorry

-- Well-Formed and Shining Trace - Definition 2.2
-- TODO: Definitions for use in proofs?
-- def varSym
-- def evSym
-- def exten

