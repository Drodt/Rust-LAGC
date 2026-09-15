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
  | pN : Place → Nat   → Place          -- Arrays
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
  | arr    : List Val → Val
 -- | struct : LVar → List (String × Val) → Val
  -- | Enums
  -- | Func : List LVar → SVal → SVaL -- Function (?)
deriving instance BEq, Repr for Val

@[elab_as_elim, induction_eliminator]
def Val.induction {motive : Val -> Sort v}
  (b : ∀ bl : Bool, motive (Val.b bl))
  (z : ∀ z : Int, motive (Val.z z))
  (refS : ∀ p : Place, ∀ bid: BId, motive (Val.refS p bid))
  (refM : ∀ p : Place, ∀ bid: BId, motive (Val.refM p bid))
  (tuple : ∀ vs : List Val, (∀ v ∈ vs, motive v) → motive (Val.tuple vs))
  (arr : ∀ vs : List Val, (∀ v ∈ vs, motive v) → motive (Val.arr vs))
  --(all_struct : ∀ x : LVar, ∀ fs : List (String × Val), (∀ f ∈ fs, motive f.snd) → motive (Val.struct x fs))
  (v : Val) : motive v := match v with
  | .b bl => b bl
  | .z n => z n
  | .refS p bid => refS p bid
  | .refM p bid => refM p bid
  | .tuple vs => tuple vs fun x _ => @induction motive b z refS refM tuple arr x
  | .arr vs => arr vs fun x _ => @induction motive b z refS refM tuple arr x
  --| .struct s fs => all_struct s fs fun x _ => @induction motive all_b all_z all_ref_s all_ref_m all_tuple all_arr all_struct x.snd

structure Renaming where
  var : LVar -> LVar
  varInv : LVar -> LVar
  borrow : BId -> BId
  borrowInv : BId → BId

@[simp] def Renaming.bijective (r : Renaming) : Prop :=
  (∀ (x y : LVar), r.var x = r.var y -> x = y)
  ∧ (∀ (y : LVar), ∃ (x : LVar), r.var x = y)
  ∧ (∀ (x y : BId), r.borrow x = r.borrow y -> x = y)
  ∧ (∀ (y : BId), ∃ (x : BId), r.borrow x = y)
  ∧ (∀ (x : LVar), r.varInv (r.var x) = x)
  ∧ (∀ x : BId, r.borrowInv (r.borrow x) = x)

@[simp] def Renaming.inv (r : Renaming) : Renaming := Renaming.mk r.varInv r.var r.borrowInv r.borrow

@[simp] theorem Renaming.inv_bij (r : Renaming) (bij : r.bijective) : r.inv.bijective := by
  simp [*] at *
  apply And.intro
  case left =>
    intro x y h
    let ⟨x', h1⟩ := bij.right.left x
    let ⟨y', h2⟩ := bij.right.left y
    rw [← h1, ← h2] at h
    let h3 := bij.right.right.right.right.left x'
    let h4 := bij.right.right.right.right.left y'
    rw [h3, h4] at h
    grind only
  case right =>
    apply And.intro
    case left =>
      intro x
      exists r.var x
      simp [*]
    case right =>
      apply And.intro
      case left =>
        intro b1 b2 h
        let ⟨b1', h1⟩ := bij.right.right.right.left b1
        let ⟨b2', h2⟩ := bij.right.right.right.left b2
        rw [← h1, ← h2] at h
        let h3 := bij.right.right.right.right.right b1'
        let h4 := bij.right.right.right.right.right b2'
        rw [h3, h4] at h
        grind only
      case right =>
        apply And.intro
        case left =>
          intro b
          exists r.borrow b
          simp [*]
        case right =>
          apply And.intro
          case left =>
            intro x
            let h := bij.right.right.right.right.left (r.varInv x)
            let inv_inj : r.varInv (r.var (r.varInv x)) = r.varInv x → r.var (r.varInv x) = x := by
              intro h'
              let ⟨x', h1⟩ := bij.right.left (r.var (r.varInv x))
              let ⟨y', h2⟩ := bij.right.left x
              rw [← h1, ← h2] at h
              let h3 := bij.right.right.right.right.left x'
              let h4 := bij.right.right.right.right.left y'
              rw [h3, h4] at h
              grind only
            simp [*]
          case right =>
            intro b
            let h := bij.right.right.right.right.right (r.borrowInv b)
            let inv_inj : r.borrowInv (r.borrow (r.borrowInv b)) = r.borrowInv b → r.borrow (r.borrowInv b) = b := by
              intro h'
              let ⟨x', h1⟩ := bij.right.right.right.left (r.borrow (r.borrowInv b))
              let ⟨y', h2⟩ := bij.right.right.right.left b
              rw [← h1, ← h2] at h
              let h3 := bij.right.right.right.right.right x'
              let h4 := bij.right.right.right.right.right y'
              rw [h3, h4] at h
              grind only
            simp [*]

@[simp] def Renaming.compose (r1 r2 : Renaming) : Renaming := Renaming.mk (fun x => r2.var (r1.var x)) (fun x => r1.varInv (r2.varInv x)) (fun x => r2.borrow (r1.borrow x)) (fun x => r1.borrowInv (r2.borrowInv x))

@[simp] def Place.rename (p : Place) (κ : LVar -> LVar) : Place := match p with
| .pV x => .pV (κ x)
| .pN p' n => .pN (p'.rename κ) n
| .pI p' f => .pI (p'.rename κ) f

theorem Place.rename_id (p : Place) : p.rename (fun x => x) = p := by
  induction p with
  | pV y =>
    simp [*]
  | pN p' n =>
    simp [*]
  | pI p' f =>
    simp [*]

theorem Place.rename_inv (p : Place) (r : Renaming) (r_bij : r.bijective) : (p.rename r.var).rename r.varInv = p := by
  induction p with
  | pV x =>
    simp [*] at *
    apply r_bij.right.right.right.right.left
  | pN p' n ih => simp [*]
  | pI => simp [*]

theorem Place.rename_compose (p : Place) (r1 r2 : Renaming) : (p.rename r1.var).rename r2.var = p.rename (r1.compose r2).var := by
  simp [*]
  induction p with
  | pV x => simp [*]
  | pN p' n ih => simp [*]
  | pI p' f ih => simp [*]

@[simp] def Val.rename : Val -> Renaming -> Val
| .tuple vs, r => .tuple (vs.map (fun v' => v'.rename r))
| .arr vs, r => .arr (vs.map (fun v' => v'.rename r))
-- | .struct s fs, r => .struct s (fs.map (fun f => ⟨ f.fst, f.snd.rename r ⟩))
| .refS p bid, r => .refS (p.rename r.var) (r.borrow bid)
| .refM p bid, r => .refM (p.rename r.var) (r.borrow bid)
| v, _ => v

theorem Val.rename_id (v : Val) : v.rename (Renaming.mk (fun y => y) (fun y => y) (fun y => y) (fun y => y)) = v := by
  induction v using Val.induction
  case b bl => simp [*]
  case z n => simp [*]
  case refS p bid =>
    simp [*]
    apply Place.rename_id
  case refM p bid =>
    simp [*]
    apply Place.rename_id
  case tuple vs ih =>
    simp [*]
    induction vs with
    | nil => simp [*]
    | cons v vs' tih =>
      simp [*]
      apply tih
      intro v' v'_in_vs
      let ih' := ih v'
      simp [*]
  case arr vs ih =>
    simp [*]
    induction vs with
    | nil => simp [*]
    | cons v vs' tih =>
      simp [*]
      apply tih
      intro v' v'_in_vs
      let ih' := ih v'
      simp [*]

theorem Val.rename_inv (v : Val) (r : Renaming) (r_bij : r.bijective) : (v.rename r).rename r.inv = v := by
  simp [*]
  induction v with
  | b bl => simp [*]
  | z n => simp [*]
  | refS p bid =>
    simp [*]
    apply And.intro
    case left =>
      apply Place.rename_inv
      exact r_bij
    case right =>
      simp [*] at r_bij
      apply r_bij.right.right.right.right.right
  | refM p bid =>
    simp [*]
    apply And.intro
    case left =>
      apply Place.rename_inv
      exact r_bij
    case right =>
      simp [*] at r_bij
      apply r_bij.right.right.right.right.right
  | tuple vs ih =>
    simp [*]
    induction vs with
    | nil => simp [*]
    | cons x xs ih' =>
      simp [*] at *
      let ih'' := ih' ih.right
      exact ih''
  | arr vs ih =>
    simp [*]
    induction vs with
    | nil => simp [*]
    | cons x xs ih' =>
      simp [*] at *
      let ih'' := ih' ih.right
      exact ih''

theorem Val.rename_compose (v : Val) (r1 r2 : Renaming) : (v.rename r1).rename r2 = v.rename (r1.compose r2) := by
  simp [*]
  induction v with
  | b bl => simp [*]
  | z n => simp [*]
  | refS p bid => simp [*, Place.rename_compose]
  | refM p bid => simp [*, Place.rename_compose]
  | tuple vs ih =>
    simp [*]
    intro v v_in_vs
    apply ih v v_in_vs
  | arr vs ih =>
    simp [*]
    intro v v_in_vs
    apply ih v v_in_vs

inductive SVal where
| sym :  SVal               -- Equivalent to *
| val : Val -> SVal

@[simp] def SVal.rename : SVal → Renaming → SVal
| .sym, _ => .sym
| .val v, r => .val (v.rename r)

theorem SVal.rename_id (sv : SVal) : sv.rename (Renaming.mk (fun y => y) (fun y => y) (fun y => y) (fun y => y)) = sv := by
  induction sv with
  | sym => simp [*]
  | val v => simp [*, Val.rename_id]

deriving instance Repr for SVal

instance : BEq SVal where
  beq : SVal -> SVal -> Bool
  | SVal.sym, SVal.sym => true
  | SVal.val v1, SVal.val v2 => v1 == v2
  | _, _ => false

@[simp] def renameOptVal : Option SVal → Renaming → Option SVal
| .some sv, r => .some (sv.rename r)
| .none, _ => .none

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

def SymState.list_find_noDups (σ : SymState) (noDups : σ.noDups) (x : LVar) (sv : SVal) : (σ.toList.find? (fun y => y.fst == x) = some (x, sv)) ↔ ((x, sv) ∈ σ.toList) := by
  let h := SymState.find_noDups σ noDups x sv
  simp [*] at h
  apply Iff.intro
  case mp =>
    intro find
    induction σ with
    | nil => simp [*] at find
    | cons x' sv' σ' ih =>
      by_cases x_eq_x' : x = x'
      case pos =>
        simp [*] at find h
        simp [*]
      case neg =>
        simp [*]
        let x'_neq_x : ¬(x' = x) := by grind only
        simp [*] at find h noDups
        let ih' := ih noDups.right h find
        exact ih'
  case mpr =>
    intro x_in_σ
    simp [*] at h
    let ⟨c, h'⟩ := h
    simp [*]
    induction σ with
    | nil => simp [*] at h'
    | cons x' sv' σ' ih =>
      simp [*] at h'
      by_cases x'_eq_x : x' = x
      case pos =>
        simp [*] at h'
        simp [*]
      case neg =>
        let x_neq_x' : ¬(x = x') := by grind only
        simp [*] at h' h noDups x_in_σ
        let ih' := ih noDups.right x_in_σ h h'
        exact ih'

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
  ∧ ∃ r : Renaming,
    r.bijective
    ∧ (∀ x ∈ σ1.dom, (¬x ∈ xs) → r.var x ∈ σ2.dom ∧ ¬(r.var x ∈ xs) ∧ σ1.find? x = renameOptVal (σ2.find? (r.var x)) r.inv)
    ∧ (∀ x ∈ σ2.dom, (¬x ∈ xs) → r.varInv x ∈ σ1.dom ∧ ¬(r.varInv x ∈ xs) ∧ σ2.find? x = renameOptVal (σ1.find? (r.varInv x)) r)

@[simp] theorem SymState.eqModR.refl (σ : SymState) (xs : List LVar) (noDups : σ.noDups) : σ.eqModR σ xs := by
  simp [*]
  apply And.intro
  case left =>
    intro x sv x_in_σ
    apply Or.inr
    exists sv
  case right =>
    let r := Renaming.mk (fun y => y) (fun y => y) (fun y => y)
    exists Renaming.mk (fun y => y) (fun y => y) (fun y => y) (fun y => y)
    apply And.intro
    case left =>
      simp [*]
    case right =>
      apply And.intro
      case left =>
        intro x1 sv1 x1_in_σ x1_not_in_xs
        simp [*]
        induction σ with
        | nil => simp [*] at x1_in_σ
        | cons x' sv' σ' ih =>
          simp [*]
          by_cases x1_eq_x' : x1 = x'
          case pos =>
            simp [*]
            induction sv' with
            | sym => simp [*]
            | val v' =>
              simp [*]
              rw [Val.rename_id]
          case neg =>
            simp [BEq.beq, *]
            simp [*] at ih x1_eq_x' noDups x1_in_σ
            let x'_neq_x1 : ¬(x' = x1) := by grind only
            let ih' := ih noDups.right x1_in_σ
            simp [*]
            simp [BEq.beq] at ih'
            exact ih'.right
      case right =>
        intro x sv x_in_σ x_not_in_xs
        simp [*]
        induction σ with
        | nil => simp [*] at x_in_σ
        | cons x' sv' σ' ih =>
          simp [*]
          by_cases x_eq_x' : x = x'
          case pos =>
            simp [*]
            induction sv' with
            | sym => simp [*]
            | val v' =>
              simp [*]
              rw [Val.rename_id]
          case neg =>
            simp [BEq.beq, *]
            simp [*] at ih x_eq_x' noDups x_in_σ
            let x'_neq_x1 : ¬(x' = x) := by grind only
            let ih' := ih noDups.right x_in_σ
            simp [*]
            simp [BEq.beq] at ih'
            exact ih'.right

@[simp] theorem SymState.eqModR.symm (σ1 σ2 : SymState) (xs : List LVar) : σ1.eqModR σ2 xs → σ2.eqModR σ1 xs := by
  simp [*]
  intro h1 h2 h3 r h4 h5 h6 h7 h8 h9 h10 h11
  apply And.intro
  case left =>
    intro x sv x_in_σ2
    apply h2 x sv x_in_σ2
  case right =>
    apply And.intro
    case left =>
      intro x sv x_in_σ1
      apply h1 x sv x_in_σ1
    case right =>
      apply And.intro
      case left =>
        intro x sv x_in_σ2 x_in_xs
        let x_in_σ1 : ∃ sv' : SVal, (x, sv') ∈ σ1.toList := by
          let h2' := h2 x sv x_in_σ2
          simp [*] at h2'
          exact h2'
        let ⟨sv', h⟩ := x_in_σ1
        let h3' := h3 x sv' h x_in_xs
        simp [*]
      case right =>
        exists r.inv
        let r_bij : r.bijective := by
          simp [*]
          apply And.intro
          case left => exact h4
          case right => exact h6
        let inv_bij := Renaming.inv_bij r r_bij
        apply And.intro
        case left =>
          simp [*] at inv_bij
          exact inv_bij
        case right =>
          apply And.intro
          case left =>
            intro x sv x_in_σ2 x_not_in_xs
            let h11' := h11 x sv x_in_σ2 x_not_in_xs
            simp [*] at h11'
            simp [*]
          case right =>
            intro x sv x_in_σ1 x_not_in_xs
            simp [*]
            let h10' := h10 x sv x_in_σ1 x_not_in_xs
            simp [*]

@[simp] theorem SymState.eqModR_trans (σ1 σ2 σ3 : SymState) (xs : List LVar) (noDups1 : σ1.noDups) (noDups3 : σ3.noDups) : σ1.eqModR σ2 xs ∧ σ2.eqModR σ3 xs → σ1.eqModR σ3 xs := by
  intro ⟨h1, h2⟩
  simp [*]
  apply And.intro
  case left =>
    intro x sv x_in_σ1
    simp [SymState.eqModR] at h1 h2
    let h1' := h1.left x sv x_in_σ1
    apply Or.by_cases h1'
    intro x_not_in_xs
    apply Or.inl x_not_in_xs
    intro ⟨sv', x_in_σ2⟩
    let h2' := h2.left x sv' x_in_σ2
    apply Or.by_cases h2'
    intro x_not_in_xs
    apply Or.inl x_not_in_xs
    intro x_in_σ3
    apply Or.inr x_in_σ3
  case right =>
    apply And.intro
    case left =>
      intro x sv x_in_σ3
      simp [SymState.eqModR] at h1 h2
      let h2' := h2.right.left x sv x_in_σ3
      apply Or.by_cases h2'
      intro x_not_in_xs
      apply Or.inl x_not_in_xs
      intro ⟨sv', x_in_σ2⟩
      let h1' := h1.right.left x sv' x_in_σ2
      apply Or.by_cases h1'
      intro x_not_in_xs
      apply Or.inl x_not_in_xs
      intro x_in_σ1
      apply Or.inr x_in_σ1
    case right =>
      apply And.intro
      case left =>
        intro x sv x_in_σ1 x_in_xs
        simp [SymState.eqModR] at h1 h2
        let h1' := h1.right.right.left x sv x_in_σ1 x_in_xs
        rw [h1']
        let ⟨sv', x_in_σ2⟩ : ∃ sv', (x, sv') ∈ σ2.toList := by
          let h1'' := h1.left x sv x_in_σ1
          simp [*] at h1''
          exact h1''
        apply h2.right.right.left x sv' x_in_σ2 x_in_xs
      case right =>
        simp [SymState.eqModR] at h1 h2
        let ⟨r1, h1'⟩ := h1.right.right.right
        let ⟨r2, h2'⟩ := h2.right.right.right
        exists r1.compose r2
        apply And.intro
        case left =>
          simp [*]
          apply And.intro
          case left =>
            intro a b h
            let r2_inj := h2'.left.left (r1.var a) (r1.var b) h
            apply h1'.left.left a b r2_inj
          case right =>
            apply And.intro
            case left =>
              intro b
              let ⟨a1, r1_surj⟩ := h2'.left.right.left b
              let ⟨a2, r2_surj⟩ := h1'.left.right.left a1
              rw [← r2_surj] at r1_surj
              exists a2
            case right =>
              apply And.intro
              case left =>
                intro a b h
                let r1_inj := h2'.left.right.right.left (r1.borrow a) (r1.borrow b) h
                apply h1'.left.right.right.left a b r1_inj
              case right =>
                intro b
                let ⟨a1, r1_surj⟩ := h2'.left.right.right.right.left b
                let ⟨a2, r2_surj⟩ := h1'.left.right.right.right.left a1
                rw [← r2_surj] at r1_surj
                exists a2
        case right =>
          apply And.intro
          case left =>
            intro x sv x_in_σ1 x_not_in_xs
            let h1'' := h1'.right.left x sv x_in_σ1 x_not_in_xs
            apply And.intro
            case left =>
              simp [*]
              let ⟨sv', r1x_in_σ2⟩ := h1''.left
              let h2'' := h2'.right.left (r1.var x) sv' r1x_in_σ2 h1''.right.left
              exact h2''.left
            case right =>
              apply And.intro
              case left =>
                simp [*]
                let ⟨sv', r1x_in_σ2⟩ := h1''.left
                let h2'' := h2'.right.left (r1.var x) sv' r1x_in_σ2 h1''.right.left
                exact h2''.right.left
              case right =>
                rw [h1''.right.right]
                simp [*] at h1''
                let ⟨sv', r1x_in_σ2⟩ := h1''.left
                let h2'' := h2'.right.left (r1.var x) sv' r1x_in_σ2 h1''.right.left
                rw [h2''.right.right]
                simp [*]
                let ⟨sv'', r2r1x_in_σ3⟩ := h2''.left
                let find_σ3_sv'' : σ3.toList.find? (fun l => l.fst == (r2.var (r1.var x))) = some ((r2.var (r1.var x)), sv'') := by
                  let find := SymState.list_find_noDups σ3 noDups3 (r2.var (r1.var x)) sv''
                  simp [*] at find
                  exact find
                simp [*] at find_σ3_sv''
                simp [*]
                induction sv'' with
                | sym => simp [*]
                | val v =>
                  simp [*, Val.rename_compose]
          case right =>
            intro x sv x_in_σ3 x_not_in_xs
            let h2'' := h2'.right.right x sv x_in_σ3 x_not_in_xs
            apply And.intro
            case left =>
              simp [*]
              let ⟨sv', r2x_in_σ2⟩ := h2''.left
              let h1'' := h1'.right.right (r2.varInv x) sv' r2x_in_σ2 h2''.right.left
              exact h1''.left
            case right =>
              rw [h2''.right.right]
              simp [*] at h2''
              apply And.intro
              case left =>
                simp [*]
                let ⟨sv', r2x_in_σ2⟩ := h2''.left
                let h1'' := h1'.right.right (r2.varInv x) sv' r2x_in_σ2 h2''.right.left
                exact h1''.right.left
              case right =>
                let ⟨sv', r2x_in_σ2⟩ := h2''.left
                let h1'' := h1'.right.right (r2.varInv x) sv' r2x_in_σ2 h2''.right.left
                rw [h1''.right.right]
                simp [*]
                let ⟨sv'', r1r2x_in_σ3⟩ := h1''.left
                let find_σ1_sv'' : σ1.toList.find? (fun l => l.fst == (r1.varInv (r2.varInv x))) = some ((r1.varInv (r2.varInv x)), sv'') := by
                  let find := SymState.list_find_noDups σ1 noDups1 (r1.varInv (r2.varInv x)) sv''
                  simp [*] at find
                  exact find
                simp [*] at find_σ1_sv''
                simp [*]
                induction sv'' with
                | sym => simp [*]
                | val v =>
                  simp [*, Val.rename_compose]
