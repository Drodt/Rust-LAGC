-- Values and states - Section 2

import Std
import Lean.Data.AssocList

open Std
open Lean

/--
  Type of variables
-/
abbrev LVar : Type := String

/--
  Type of places
-/
inductive Place where
  | pV : LVar → Place
  | pN : Nat  → Place
  | pP : Place → Place
deriving instance BEq, Repr for Place

/--
  Type of borrow identifiers
-/
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
  -- | Enum
  -- | Func : List LVar → SVal → SVaL -- Function
deriving instance BEq, Repr for SVal

open SVal

/--
  Symbolic state is a list of mappings Var → SVal
  Consider the usage of list-specific operations like map via toList
-/
abbrev SymState := AssocList LVar SVal

-- TODO: Consider cases with arrays, tuples, strcuts, enums (p.2)
/--
  State update
-/
def update (σ : SymState) (u : LVar × SVal) : SymState := match σ with
  | .nil           =>
    σ.insert u.fst u.snd
  | .cons x y xys  =>
    if x == u.fst then σ.replace u.fst u.snd else .cons x y (update xys u)

/--
  Symbolic variables of a state
-/
def symb (σ : SymState) : List LVar :=
  (σ.toList.filter (fun p => p.snd == sym)).map (fun c => c.fst)
