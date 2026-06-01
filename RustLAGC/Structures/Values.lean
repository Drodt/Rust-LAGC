/-
  Work Package A2

  Based on section 2
-/

import Std
import Lean.Data.AssocList

open Std
open Lean

/--
  Type of variables in LAGC
-/
abbrev LVar : Type := String

/--
  Type of places
-/
inductive Place where
  | pV : LVar  → Place          -- Var
  | pN : Nat   → Place          -- Arrays
  | pI : Place → String → Place -- Structs
deriving instance BEq, Repr for Place

/--
  Type of borrow identifiers
-/
-- TODO: Simplify to String?
inductive BId where
  | bId : LVar → BId
deriving instance BEq, Repr for BId

/--
  Type of starred values
-/
inductive SVal where
  | sym    : SVal               -- Equivalent to *
  | b      : Bool  → SVal       -- Mapping Lean types directly to SVal
  | z      : Int   → SVal
  | refS   : Place → BId → SVal -- Shared reference
  | refM   : Place → BId → SVal -- Mutable reference
  | tuple  : List SVal  → SVal
  | arr    : Array SVal → SVal
  | struct : LVar × List (Place × SVal) → SVal 
  -- | Enums
  -- | Func : List LVar → SVal → SVaL -- Function (?)
deriving instance BEq, Repr for SVal

open SVal

/--
  Symbolic state is a list of mappings Var → SVal
  Consider the usage of list-specific operations like map via toList
-/
abbrev SymState := AssocList LVar SVal

/--
  Constructor abbreviation
-/
def SymState.mk (x : List (LVar × SVal)) : SymState := x.toAssocList'

-- TODO: Consider cases with arrays, tuples, strcuts, enums (p.2)
/--
  State update
-/
def SymState.update (σ : SymState) (u : LVar × SVal) : SymState := match σ with
  | .nil           =>
    σ.insert u.fst u.snd
  | .cons x y xys  =>
    if x == u.fst then σ.replace u.fst u.snd else .cons x y (update xys u)

/--
  Symbolic variables of a state
-/
def SymState.symb (σ : SymState) : List LVar :=
  (σ.toList.filter (fun p => p.snd == sym)).map (fun c => c.fst)
