import Std
import Lean.Data.AssocList

open Std
open Lean

abbrev LVar : Type := String

inductive Place where
  | pV : LVar → Place
  | pN : Nat  → Place
deriving instance BEq, Repr for Place

inductive BId where
  | bId : LVar → BId
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
  | struct : LVar × List (Place × SVal) → SVal 
  -- | Enum
  -- | Func : List LVar → SVal → SVaL -- Function
deriving instance BEq, Repr for SVal

open SVal

/--
  Symbolic state
  TODO: Change data structure?
-/
abbrev SymState :=
  AssocList LVar SVal

-- State update
-- TODO: Consider cases with arrays, tuples, strcuts, enums (p.2)
def update (σ : SymState) (u : LVar × SVal) : SymState := match σ with
  | .nil       => σ.insert u.fst u.snd
  | .cons x y xys  => if x == u.fst then σ.replace u.fst u.snd else .cons x y (update xys u)

/--
  Symbolic variables of a state
-/
def symb (σ : SymState) : List LVar :=
  (σ.toList.filter (fun p => p.snd == sym)).map (fun c => c.fst)
