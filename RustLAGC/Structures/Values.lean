/-
  Work Package A2

  Based on section 2
-/

import Std
import RustLAGC.Data.AssocList

open Std
open Lean

/--
  Type of variables in LAGC. Abbreviation of type String.
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
inductive BId where
  | mk : LVar → BId
deriving instance BEq, Repr for BId

/--
  Type of starred values
-/
inductive Val where
  | b      : Bool  → Val       -- Mapping Lean types directly to SVal
  | z      : Int   → Val
  | refS   : Place → BId → Val -- Shared reference
  | refM   : Place → BId → Val -- Mutable reference
  | tuple  : List Val  → Val
  | arr    : Array Val → Val
  | struct : LVar × List (Place × Val) → Val
  -- | Enums
  -- | Func : List LVar → SVal → SVaL -- Function (?)
deriving instance BEq, Repr for Val

inductive SVal where
| sym :  SVal               -- Equivalent to *
| val : Val -> SVal

deriving instance Repr for SVal

instance : BEq SVal where
  beq : SVal -> SVal -> Bool
  | SVal.sym, SVal.sym => true
  | SVal.val v1, SVal.val v2 => v1 == v2
  | _, _ => false

open SVal

/--
  Symbolic state is a list of mappings Var → SVal
  Consider the usage of list-specific operations like `map` via `toList`
-/
abbrev SymState := AssocList LVar SVal

/--
  Constructor abbreviation
-/
def SymState.mk (x : List (LVar × SVal)) : SymState := x.toAssocList

/--
  State update
-/
def SymState.updateVar (σ : SymState) (x : LVar)  (v : SVal) : SymState := σ.insert x v

-- TODO: Consider cases with arrays, tuples, strcuts, enums (p.2)
-- Not trivial, requires wild typing stuff
--def SymState.updatePlace (σ : SymState) (u : Place × SVal) : SymState := match σ with
--  | .nil => sorry
--  | .cons x y xys => sorry

/--
  Symbolic variables of a symbolic state
-/
@[simp] def SymState.symb (σ : SymState) : List LVar :=
  (σ.toList.filter (fun p => p.snd == sym)).map (fun c => c.fst)

/--
  Domain of a symbolic state
-/
@[simp] def SymState.dom (σ : SymState) : List LVar :=
  σ.toList.map fun x => x.fst

@[simp] def SymState.isConcrete (σ : SymState) : Bool := σ.symb.isEmpty

@[simp] theorem SymState.isConcrete_empty (σ : SymState) (h : σ = AssocList.nil) : σ.isConcrete := by
  simp [SymState.isConcrete, SymState.symb]
  have hl : σ.toList = [] := by
    rw [h]
    simp
  rw [hl]
  simp

@[simp] def SymState.noDups : SymState -> Bool
| AssocList.nil => true
| AssocList.cons x _ σ' => ¬σ'.contains x ∧ noDups σ'

@[simp] def SymState.extends (σ1 σ2 : SymState) : Bool := σ1.all
  (fun x v => σ2.find? x == some v)

instance : BEq SymState where
  beq (σ1 σ2 : SymState) : Bool := σ1.dom == σ2.dom /\ σ2.extends σ1

@[simp] theorem SymState.inSymb_inDom (σ : SymState) (x : LVar) (h : x ∈ σ.symb) : x ∈ σ.dom := by
  simp [*] at h
  let ⟨sv, ⟨h1, _⟩⟩ := h
  simp [*]
  exists sv

@[simp] theorem SymState.inSymb_isSym (σ : SymState) (x : LVar) (h : x ∈ σ.symb) : (x, sym) ∈ σ.toList := by
  simp [*] at h
  let ⟨sv, h1⟩ := h
  let h2 : sv = sym := by
    let h2 := h1.right
    simp [(· == ·)] at h2
    induction sv with
    | sym => simp [*]
    | val v =>
      simp [*] at h2
  simp [*] at h1
  exact h1.left
