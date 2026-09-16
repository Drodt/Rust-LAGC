/-
  Work Package A2

  Based on section 2
-/

import Std

import RustLAGC.Data.AssocList
import RustLAGC.Structures.Values
import RustLAGC.Structures.Rust

open Std
open Lean
open SVal

/-
  /--
    Type of events

    Alternative to string-based events
  -/
  inductive Event where
    | invEv
    | compREv
-/

/--
  Inductive type of event parameters
-/
inductive EvPar where
  | var : LVar → EvPar
  | val : Val → EvPar

deriving instance BEq for EvPar

/--
  Inductive type of event markers
-/
inductive EventMarker where
  | mk : String → List EvPar → EventMarker

@[simp] def EventMarker.vars (ev : EventMarker) : List LVar := match ev with
| mk _ eps => eps.filterMap (fun ep => match ep with
  | EvPar.var x => some x
  | _ => none
)

deriving instance BEq for EventMarker

inductive TraceElem where
| state : SymState → TraceElem
| event : SymState → EventMarker → SymState → TraceElem

deriving instance BEq for TraceElem
deriving instance Inhabited for TraceElem

@[simp] def TraceElem.isState : TraceElem -> Bool
| TraceElem.state _ => true
| _ => false

@[simp] def TraceElem.isEvent : TraceElem -> Bool
| TraceElem.event _ _ _=> true
| _ => false

/--
  Construction of symbolic traces
-/
abbrev SymTrace := List TraceElem

def ε : SymTrace := List.nil

open EventMarker

/--
  Singleton trace
-/
def SymTrace.singleton (s : SymState) : SymTrace := [ TraceElem.state s ]

/-
  Symbolic chop; stitching together two traces
-/
def chop (a b : SymTrace) : Option SymTrace := match a, b with
| [] , _ => none
| _, [] => none
| τ1, σ :: τ2 => if τ1.getLast! == σ then some (τ1 ++ τ2) else none

/-
  Concretization Mapping
-/
-- def concrete (x : Var) : SVal := sorry

-- Trace Concretization
-- def concrete (x : Var) : SVal := sorry
-- TODO: Values zu Expression abbilden per Funktion oder Typsystem
inductive ContMarker where
  | mk : RExp → ContMarker

-- Property on 1:3
-- Trace compostion ensures that all generated traces have a state on either side of each event marker

-- Well-Formed and Shining Trace - Definition 2.2
inductive varSym : Prop
  | s
inductive evSym  : Prop
inductive exten  : Prop

-- Example 2.3
def σ₀: SymState := .mk [("X", sym), ("y", val (Val.b false))]
#check [TraceElem.event σ₀ ⟨"ev₀", [EvPar.var "X"]⟩ (σ₀.updateVar "y" (val (Val.b true)))]

-- Other examples
-- Empty trace
#check ε

abbrev ConcrMap := AssocList LVar Val

@[simp] def ConcrMap.dom (ρ : ConcrMap) : List LVar := ρ.toList.map fun x => x.fst

@[simp] def ConcrMap.noDups : ConcrMap -> Bool
| AssocList.nil => true
| AssocList.cons x _ ρ' => ¬ρ'.contains x ∧ noDups ρ'

@[simp] def ConcrMap.isFor (ρ : ConcrMap) (σ : SymState) : Bool :=
  σ.symb.all (fun X => ρ.contains X)
  /\ σ.dom.all (fun x => ρ.contains x == (σ.find? x == some SVal.sym))

theorem ConcrMap.find_no_dups (ρ : ConcrMap) (noDups : ρ.noDups) (x : LVar) (v : Val) : (ρ.find? x = some v) ↔ ((x, v) ∈ ρ.toList) := by
  simp [*]
  apply Iff.intro
  case mp =>
    intro ⟨c, h⟩
    induction ρ with
    | nil => simp [*] at h
    | cons x' v' ρ' ih =>
      simp [*]
      by_cases x_eq_x' : x = x'
      case pos =>
        simp [*] at *
        let h' := h.right.symm
        apply Or.inl h'
      case neg =>
        simp [*] at noDups h
        simp [*]
        let x'_neq_x : ¬(x' = x) := by grind only
        simp [*] at h
        let ih' := ih noDups.right h
        exact ih'
  case mpr =>
    intro x_in_ρ
    exists x
    induction ρ with
    | nil => simp [*] at x_in_ρ
    | cons x' v' ρ' ih =>
      by_cases x_eq_x' : x = x'
      case pos =>
        simp [*] at *
        by_cases v = v'
        case pos => simp [*]
        case neg =>
          simp [*] at x_in_ρ
          let nd := noDups.left x' v x_in_ρ
          simp [*] at nd
      case neg =>
        let x'_neq_x : ¬(x' = x) := by grind only
        simp [*] at *
        simp [*]

theorem ConcrMap.list_find_noDups (ρ : ConcrMap) (noDups : ρ.noDups) (x : LVar) (v : Val) : (ρ.toList.find? (fun y => y.fst == x) = some (x, v)) ↔ ((x, v) ∈ ρ.toList) := by
  let h := ConcrMap.find_no_dups ρ noDups x v
  simp [*] at h
  apply Iff.intro
  case mp =>
    intro find
    induction ρ with
    | nil => simp [*] at find
    | cons x' v' σ' ih =>
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
    induction ρ with
    | nil => simp [*] at h'
    | cons x' v' σ' ih =>
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

@[simp] def ConcrMap.toState (ρ : ConcrMap) : SymState := ρ.mapVal (fun _ v => (SVal.val v))

@[simp] def ConcrMap.applyOnState (ρ : ConcrMap) (σ : SymState) : SymState :=
  (ρ.toState.toList ++ (σ.toList.filter (fun (x, _) => ¬ρ.contains x))).toAssocList

def ρ₀ : ConcrMap := [("X", Val.z 3)].toAssocList
#eval ConcrMap.applyOnState ρ₀ σ₀

@[simp] theorem ConcrMap.toState_isConcrete (ρ : ConcrMap) : ρ.toState.isConcrete := by
  simp [*]
  intro x1 sv x2 v h1 h2 h3
  rw [← h3]
  rfl

@[simp] theorem ConcrMap.applyOnState_isConcrete (ρ : ConcrMap) (σ : SymState) (h : ρ.isFor σ) : (ρ.applyOnState σ).isConcrete :=
  by induction σ with
  | nil =>
    simp [*]
    intro x1 sv x2 v h1 h2 h3
    rw [← h3]
    rfl
  | cons x v σ'' ih =>
    simp [*]
    apply And.intro
    intro x1 sv x2 v h1 h2 h3
    rw [← h3]
    rfl
    apply And.intro
    intro h1
    simp [*] at h
    exact h.left.left
    intro x1 sv h1 h2
    simp [*] at h
    let h3 := h.left.right x1 sv h1
    simp [*] at h3
    exact h3

@[simp] def ConcrMap.applyOnEvent (ρ : ConcrMap) (ev : EventMarker) : EventMarker :=
  (.mk ev.1
      (ev.2.map (fun e => match e with
        | EvPar.var x => if let some v := ρ.find? x
            then EvPar.val v
            else e
        | EvPar.val _ => e
        )))

@[simp] def ConcrMap.applyOnTraceElem (ρ : ConcrMap) (te : TraceElem) : TraceElem := match te with
| TraceElem.state σ => TraceElem.state (ConcrMap.applyOnState ρ σ)
| TraceElem.event σ1 ev σ2 => TraceElem.event (ρ.applyOnState σ1) (ρ.applyOnEvent ev) (ρ.applyOnState σ2)

@[simp] theorem ConcrMap.applyOnTraceElem_kindStaysSame (ρ : ConcrMap) (t : TraceElem) : (ρ.applyOnTraceElem t).isState = t.isState ∧ (ρ.applyOnTraceElem t).isEvent = t.isEvent := by
  simp [*]
  apply And.intro
  case left =>
    induction t with
    | state σ =>
      simp [*]
    | event ev =>
      simp [*]
  case right =>
    induction t with
    | state σ =>
      simp [*]
    | event ev =>
      simp [*]

@[simp] def ConcrMap.applyOnTrace (ρ : ConcrMap) (τ : SymTrace) : SymTrace :=
  τ.map (fun te => ρ.applyOnTraceElem te)

namespace SymTrace

@[simp] def states (τ : SymTrace) : List SymState :=
  match τ with
  | [] => []
  | TraceElem.state σ :: τ' => σ :: (states τ')
  | TraceElem.event σ1 _ σ2 :: τ' => [σ1, σ2] ++ (states τ')

@[simp] def events (τ : SymTrace) : List EventMarker :=
  τ.filterMap (fun te => match te with
  | TraceElem.event _ ev _ => some ev
  | _ => none)

@[simp] def symb (τ : SymTrace) : List LVar :=
  τ.states.foldl (fun s σ => s ++ σ.symb) []

@[simp] def eventsSurroundedByFittingStates (τ : SymTrace) : Bool := match τ with
| TraceElem.state _ :: τ' => eventsSurroundedByFittingStates τ'
| TraceElem.event σ1 _ σ2 :: τ' => σ2.extends σ1 ∧ eventsSurroundedByFittingStates τ'
| [] => true

@[simp] def noDups (τ : SymTrace) : Bool :=
  τ.states.all SymState.noDups

@[simp] def wellFormed (τ : SymTrace) : Bool :=
  τ.states.all (fun σ => σ.dom.all (fun x => σ.symb.contains x || ¬τ.symb.contains x))
  ∧ τ.events.all (fun ev => ev.vars.all (fun x => τ.symb.contains x))
  ∧ τ.eventsSurroundedByFittingStates

@[simp] def isConcrete (τ : SymTrace) : Bool :=
  τ.wellFormed ∧ τ.symb.isEmpty

end SymTrace

@[simp] def ConcrMap.isForTr (ρ : ConcrMap) (τ : SymTrace) : Bool :=
  τ.states.all ρ.isFor

theorem ConcrMap.isForTr_cons (ρ : ConcrMap) (t : TraceElem) (τ : SymTrace) (hFor : ρ.isForTr (t :: τ)) : ρ.isForTr τ := by
  simp [*] at *
  induction t with
  | state σ =>
    simp [*] at hFor
    exact hFor.right
  | event σ ev σ' =>
    simp [*] at *
    exact hFor.right.right

@[simp] theorem ConcrMap.applyOnTr_symb_isEmpty (ρ : ConcrMap) (τ : SymTrace) (hFor : ρ.isForTr τ) (noDups : τ.noDups) : (ρ.applyOnTrace τ).symb.isEmpty := by
  simp [*]
  intro σ σ_in_τ x sv x_in_σ
  induction τ with
  | nil => simp [*] at *
  | cons t τ' ih =>
    simp [*] at *
    induction t with
    | state σ' =>
      simp [*] at *
      by_cases σ_eq_ρ_of_σ' : σ = ρ.applyOnState σ'
      case pos =>
        let for_σ' : ρ.isFor σ' := by
          simp [*]
          apply hFor.left
        let ρ_of_σ'_concr := ConcrMap.applyOnState_isConcrete ρ σ' for_σ'
        simp [*] at σ_in_τ ρ_of_σ'_concr x_in_σ
        by_cases a_b_in_ρ : (∃ a b, (a, b) ∈ ρ.toList ∧ a = x ∧ val b = sv)
        case pos =>
          let ⟨a, ⟨b, ⟨a_b_in_ρ, ⟨a_eq_x, val_b_eq_sv⟩⟩⟩⟩ := a_b_in_ρ
          rw [← val_b_eq_sv]
          simp [BEq.beq]
        case neg =>
          simp [*] at x_in_σ for_σ'
          let h := for_σ'.right x sv x_in_σ.left
          induction sv with
          | sym =>
            simp [*]
            let find := SymState.list_find_noDups σ' noDups.left x sym
            simp [*] at find
            rw [find] at h
            simp [BEq.beq, *, Option.instBEq.beq] at h
            let ⟨c, h'⟩ := h
            let h'' := x_in_σ.right x c h'
            simp [*] at h''
          | val v => simp [*, BEq.beq]
      case neg =>
        simp [*] at σ_eq_ρ_of_σ'
        simp [*] at σ_in_τ
        apply ih hFor.right noDups.right σ_in_τ
    | event σ1 _ σ2 =>
      simp [*] at σ_in_τ hFor
      by_cases σ_eq_ρ_of_σ1 : σ = ρ.applyOnState σ1
      case pos =>
        let for_σ1 : ρ.isFor σ1 := by
          simp [*]
          apply hFor.left
        let ρ_of_σ1_concr := ConcrMap.applyOnState_isConcrete ρ σ1 for_σ1
        simp [*] at σ_in_τ ρ_of_σ1_concr x_in_σ
        by_cases a_b_in_ρ : (∃ a b, (a, b) ∈ ρ.toList ∧ a = x ∧ val b = sv)
        case pos =>
          let ⟨a, ⟨b, ⟨a_b_in_ρ, ⟨a_eq_x, val_b_eq_sv⟩⟩⟩⟩ := a_b_in_ρ
          rw [← val_b_eq_sv]
          simp [BEq.beq]
        case neg =>
          simp [*] at x_in_σ for_σ1
          let h := for_σ1.right x sv x_in_σ.left
          induction sv with
          | sym =>
            simp [*]
            simp [*] at noDups
            let find := SymState.list_find_noDups σ1 noDups.left x sym
            simp [*] at find
            rw [find] at h
            simp [BEq.beq, *, Option.instBEq.beq] at h
            let ⟨c, h'⟩ := h
            let h'' := x_in_σ.right x c h'
            simp [*] at h''
          | val v => simp [*, BEq.beq]
      case neg =>
        by_cases σ_eq_ρ_of_σ2 : σ = ρ.applyOnState σ2
        case pos =>
          let for_σ2 : ρ.isFor σ2 := by
            simp [*]
            apply hFor.right.left
          let ρ_of_σ2_concr := ConcrMap.applyOnState_isConcrete ρ σ2 for_σ2
          simp [*] at σ_in_τ ρ_of_σ2_concr x_in_σ
          by_cases a_b_in_ρ : (∃ a b, (a, b) ∈ ρ.toList ∧ a = x ∧ val b = sv)
          case pos =>
            let ⟨a, ⟨b, ⟨a_b_in_ρ, ⟨a_eq_x, val_b_eq_sv⟩⟩⟩⟩ := a_b_in_ρ
            rw [← val_b_eq_sv]
            simp [BEq.beq]
          case neg =>
            simp [*] at x_in_σ for_σ2
            let h := for_σ2.right x sv x_in_σ.left
            induction sv with
            | sym =>
              simp [*]
              simp [*] at noDups
              let find := SymState.list_find_noDups σ2 noDups.right.left x sym
              simp [*] at find
              rw [find] at h
              simp [BEq.beq, *, Option.instBEq.beq] at h
              let ⟨c, h'⟩ := h
              let h'' := x_in_σ.right x c h'
              simp [*] at h''
            | val v => simp [*, BEq.beq]
        case neg =>
          simp [*] at σ_eq_ρ_of_σ1 σ_eq_ρ_of_σ2
          simp [*] at σ_in_τ hFor ih noDups
          apply ih hFor.right.right noDups.right.right σ_in_τ

theorem ConcrMap.applyOnTrace_allStatesAgree (ρ : ConcrMap) (τ : SymTrace) (hFor : ρ.isForTr τ) (noDups : τ.noDups) :
  (ρ.applyOnTrace τ).states.all (fun σ => σ.dom.all (fun x => σ.symb.contains x || ¬(ρ.applyOnTrace τ).symb.contains x)) := by
  simp [*]
  intro σ σ_in_ρ_τ x sv x_in_σ
  let concr := applyOnTr_symb_isEmpty ρ τ hFor noDups
  simp [*] at concr
  let concr_σ := concr σ σ_in_ρ_τ x
  let not_sym : ¬(∃ x_1, (x, x_1) ∈ AssocList.toList σ ∧ (x_1 == sym) = true) := by
    simp [*]
    exact concr_σ
  simp [*]
  intro σ' σ'_in_ρ_τ sv' x_in_σ'
  apply concr σ' σ'_in_ρ_τ x sv' x_in_σ'

theorem ConcrMap.applyOnTrace_allEventVarsSym (ρ : ConcrMap) (τ : SymTrace) (hFor : ρ.isForTr τ) (hWF : τ.wellFormed) (hNoDups : ρ.noDups) :
  (ρ.applyOnTrace τ).events.all (fun ev => ev.vars.all (fun x => (ρ.applyOnTrace τ).symb.contains x)) := by
  simp [*]
  intro t t_in_τ
  induction t with
  | state σ =>
    simp [*]
  | event σ1 ev σ2 =>
    simp [*]
    intro ep h1
    induction ep with
    | val => simp [*]
    | var x =>
      simp [*]
      let x_in_τ_symb : x ∈ τ.symb := by
        simp [*]
        simp [*] at hWF
        let h2 := hWF.right.left (TraceElem.event σ1 ev σ2)
        simp [*] at h2
        let h2 := h2 (EvPar.var x)
        simp [*] at h2
        exact h2
      let x_in_ρ_dom : x ∈ ρ.dom := by
        simp [*]
        simp [*] at x_in_τ_symb
        simp [*] at hFor
        let ⟨symb, ⟨⟨σ, ⟨σ_in_τ, h3⟩⟩, x_in_symb⟩⟩ := x_in_τ_symb
        let hFor := hFor σ
        simp [*] at hFor
        let h6 := hFor.left x (SVal.sym)
        simp [*] at h6
        let h7 : (x, sym) ∈ σ.toList := by
          let x_in_σ_symb : x ∈ σ.symb := by
            simp [*]
          apply SymState.inSymb_isSym
          simp [*]
        exact h6
      simp [*] at x_in_ρ_dom
      let ⟨v, hv⟩ := x_in_ρ_dom
      let h8 : ρ.toList.find? (fun y => y.fst == x) = some (x, v) := by
        let find := ConcrMap.list_find_noDups ρ hNoDups x v
        simp [*] at find
        simp [*]
      simp [*] at h8
      simp [*]

theorem ConcrMap.applyOnTrace_allEventsSurrounded (ρ : ConcrMap) (τ : SymTrace) (hFor : ρ.isForTr τ) (hWF : τ.wellFormed) :
  (ρ.applyOnTrace τ).eventsSurroundedByFittingStates := by
  simp [*]
  induction τ with
  | nil => simp [*]
  | cons t τ' ih =>
    simp [*]
    induction t with
    | state σ =>
      induction τ' with
      | nil => simp [*]
      | cons t' τ'' ih' =>
        induction t' with
        | state σ' =>
          let ρ_for_τ' := ConcrMap.isForTr_cons ρ (TraceElem.state σ) (TraceElem.state σ' :: τ'') hFor
          let ih1 := ih ρ_for_τ'
          sorry
        | event ev =>
          sorry
    | event ev =>
      simp [*] at hWF
      sorry


@[simp] theorem ConcrMap.applyOnTrace_isConcrete (ρ : ConcrMap) (τ : SymTrace) (hFor : ρ.isForTr τ) (hWF : τ.wellFormed) (hNoDups : ρ.noDups) (noDups : τ.noDups) : (ρ.applyOnTrace τ).isConcrete := by
  simp [*]
  apply And.intro
  case left =>
    apply And.intro
    case left =>
      let h1 := ConcrMap.applyOnTrace_allStatesAgree ρ τ hFor noDups
      simp [*] at h1
      intro σ h2
      let h1' := h1 σ
      simp [*] at h1'
      exact h1'
    case right =>
      apply And.intro
      case left =>
        intro t h1
        let h2 := ConcrMap.applyOnTrace_allEventVarsSym ρ τ hFor hWF hNoDups
        simp [*] at h2
        let h2' := h2 t
        simp [*] at h2'
        simp [*]
      case right =>
        let h1 := ConcrMap.applyOnTrace_allEventsSurrounded ρ τ hFor hWF
        simp [*] at h1
        simp [*]
  case right =>
    intro σ σ_in_ρ_τ x sv x_in_σ
    let concr := ConcrMap.applyOnTr_symb_isEmpty ρ τ hFor noDups
    simp [*] at concr
    apply concr σ σ_in_ρ_τ x sv x_in_σ
