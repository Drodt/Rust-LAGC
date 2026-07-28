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

@[simp] def SymState.find_noDups (σ : SymState) (noDups : σ.noDups) (x : LVar) (sv : SVal) : (σ.find? x = some sv) ↔ ((x, sv) ∈ σ.toList) := by
  simp [*]
  apply Iff.intro
  case mp =>
    intro h
    induction σ with
    | nil => simp [*] at h
    | cons x' sv' σ' ih =>
      simp [*] at noDups
      simp [*] at ih
      by_cases x_eq_x' : x = x'
      case pos =>
        simp [*]
        let ⟨a, h'⟩ := h
        simp [*] at h'
        simp [*]
      case neg =>
        simp [*]
        let ⟨a, h'⟩ := h
        let ih' := ih a
        simp [*] at h'
        simp [*] at ih'
        let ne : ¬ x'=x := by
          grind only
        simp [*] at h'
        simp [*]
  case mpr =>
    intro h
    induction σ with
    | nil => simp [*] at h
    | cons x' sv' σ' ih =>
      simp [*]
      exists x
      simp [*]
      by_cases x' = x
      case pos x_eq_x' =>
        simp [*]
        simp [*] at noDups
        let noDups' := noDups.left x sv
        simp [*] at h
        by_cases (x, sv) ∈ σ'.toList
        case pos h' =>
          simp [*] at noDups'
        case neg h' =>
          simp [*] at h
          simp [*]
      case neg ne =>
        simp [*]
        simp [*] at noDups
        simp [*] at ih
        simp [*] at h
        let ne' : ¬x=x' := by grind only
        simp [*] at h
        simp [*] at ih
        let ⟨a, ih'⟩ := ih
        simp [*]
        grind only [→ List.find?_some]

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

@[simp] def SymState.eqModR (σ1 σ2 : SymState) (xs : List LVar) : Prop :=
  σ1.dom.all (fun x => (x ∈ xs) -> x ∈ σ2.dom)
  ∧ σ2.dom.all (fun x => (x ∈ xs) -> x ∈ σ1.dom)
  ∧ (∀ x ∈ σ1.dom, (x ∈ xs) -> σ1.find? x = σ2.find? x)
  ∧ ∃ κ : AssocList LVar LVar,
    (∀ x ∈ σ1.dom, ¬x ∈ xs -> ∃ y, (x, y) ∈ κ.toList) -- domain
    ∧ (∀ x1 ∈ σ1.dom, ¬x1 ∈ xs -> ∀ x2 ∈ σ1.dom, ¬x2 ∈ xs -> ∀ y ∈ σ2.dom, ¬y ∈ xs → (x1, y) ∈ κ.toList ∧ (x2, y) ∈ κ.toList → x1 = x2) -- injective
    ∧ (∀ x ∈ σ2.dom, ¬x ∈ xs -> ∃ y, (y, x) ∈ κ.toList) -- surjective
    ∧ (∀ x ∈ σ1.dom, ¬x ∈ xs -> ∀ y1 ∈ σ2.dom, ¬y1 ∈ xs -> ∀ y2 ∈ σ2.dom, ¬y2 ∈ xs → (x, y1) ∈ κ.toList ∧ (x, y2) ∈ κ.toList → y1 = y2) -- function
    ∧ (∀ x ∈ σ1.dom, (¬x ∈ xs) -> σ1.find? x = σ2.find? (κ.find? x).get!)

@[simp] def SymState.eqModR.refl (σ : SymState) (xs : List LVar) (noDups : σ.noDups) : σ.eqModR σ xs := by
  simp [*]
  apply And.intro
  case left =>
    intro x sv x_in_σ
    apply Or.inr
    exists sv
  case right =>
    exists σ.mapVal (fun y _ => y)
    apply And.intro
    case left =>
      intro x sv x_in_σ x_in_xs
      let h : ((σ.mapVal (fun y _ => y)).find? x).get! = x := by
        simp [*]
        induction σ with
        | nil => simp [*] at x_in_σ
        | cons x' sv' σ' ih =>
          simp [*] at noDups
          simp [*] at ih
          simp [*]
          by_cases x_eq_x' : x = x'
          case pos =>
            simp [*]
          case neg =>
            simp [*] at x_in_σ
            simp [*] at ih
            grind only [= List.find?_cons]
      simp [*] at h
      simp [*]
      exists sv
    case right =>
      apply And.intro
      case left =>
        intro x sv x_in_σ x_not_in_xs x' sv' x'_in_σ x'_not_in_xs y sy y_in_σ y_not_in_xs xy_in_σ x'y_in_σ


        sorry
      case right =>
        sorry

@[simp] def SymState.eqModR.symm (σ1 σ2 : SymState) (xs : List LVar) (noDups1 : σ1.noDups) (noDups2 : σ2.noDups) : σ1.eqModR σ2 xs → σ2.eqModR σ1 xs := by
  simp [*]
  intro h1 h2 h3 κ h4
  apply And.intro
  case left =>
    intro x sv x_in_σ2
    let h2' := h2 x sv x_in_σ2
    exact h2'
  case right =>
    apply And.intro
    case left =>
      intro x sv x_in_σ1
      let h1' := h1 x sv x_in_σ1
      exact h1'
    case right =>
      apply And.intro
      case left =>
        intro x sv x_in_σ2 x_in_xs
        let x_in_σ1 : ∃ a, (x, a) ∈ σ1.toList := by
          let h2' := h2 x sv x_in_σ2
          simp [*] at h2'
          exact h2'
        let ⟨a, x_in_σ1'⟩ := x_in_σ1
        let h3' := h3 x a
        simp [*]
      case right =>
        exists (κ.toList.map (fun (x,x') => (x',x))).toAssocList
        intro x sv x_in_σ2 x_not_in_xs
        simp [*]

        /- by_cases x ∈ σ1.dom
        case pos x_in_σ1 =>
          simp [*] at x_in_σ1
          let ⟨sv', h⟩ := x_in_σ1
          let σ2_find_sv : σ2.find? x = some sv := by
            rw [SymState.find_noDups]
            exact x_in_σ2
            exact noDups2
          simp [*] at σ2_find_sv
          let ⟨a, h'⟩ := σ2_find_sv
          simp [*]
          let ⟨b, h''⟩ := x_in_σ1
          let σ1_find_b : σ1.find? x = some b := by
            rw [SymState.find_noDups]
            exact h''
            exact noDups1
          simp [*] at σ1_find_b
          let ⟨c, h'''⟩ := σ1_find_b
          simp [*]
          sorry
        case neg x_not_in_σ1 =>
          sorry -/
