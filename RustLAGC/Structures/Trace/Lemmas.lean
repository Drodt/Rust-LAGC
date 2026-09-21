import RustLAGC.Structures.Trace.Basic

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

open SVal

theorem ConcrMap.list_comp_find_noDups (ρ : ConcrMap) (noDups : ρ.noDups) (x : LVar) (v : Val) : (ρ.toList.find? ((fun x_1 ↦ x_1.fst == x) ∘ fun x ↦ (x.fst, val x.snd)) = some (x, v)) ↔ ((x, v) ∈ ρ.toList) := by
  induction ρ with
  | nil => simp [*]
  | cons x' v' ρ' ih =>
    simp [*]
    apply Iff.intro
    case mp =>
      intro h
      by_cases x_eq_x' : x = x'
      case pos =>
        simp [*] at h
        simp [*]
      case neg =>
        simp [*]
        let x'_neq_x : ¬(x' = x) := by grind only
        simp [*] at h noDups
        let ih' := ih noDups.right
        apply ih'.mp h
    case mpr =>
      intro h
      by_cases x_eq_x' : x = x'
      case pos =>
        simp [*] at h noDups
        let nd := noDups.left x v
        simp [*]
        by_cases v = v'
        case pos p => simp [*]
        case neg np =>
          simp [*] at h
          simp [*] at nd
      case neg =>
        let x'_neq_x : ¬(x' = x) := by grind only
        simp [*] at h noDups
        let ih' := ih noDups.right
        simp [*]

@[simp] theorem ConcrMap.toState_isConcrete (ρ : ConcrMap) : ρ.toState.isConcrete := by
  simp [*]
  intro x1 sv x2 v h1 h2 h3
  rw [← h3]
  grind only

-- Prop. 2.7.
@[simp] theorem ConcrMap.applyOnState_isConcrete (ρ : ConcrMap) (σ : SymState) (h : ρ.isFor σ) : (ρ.applyOnState σ).isConcrete :=
  by induction σ with
  | nil =>
    simp [*]
    intro x1 sv x2 v h1 h2 h3
    rw [← h3]
    grind only
  | cons x v σ'' ih =>
    simp [*]
    apply And.intro
    intro x1 sv x2 v h1 h2 h3
    rw [← h3]
    grind only
    apply And.intro
    intro h1
    simp [*] at h
    exact h.left.left
    intro x1 sv h1 h2
    simp [*] at h
    let h3 := h.left.right x1 sv h1
    simp [*] at h3
    exact h3

theorem ConcrMap.applyOnState_not_in_ρ (ρ : ConcrMap) (σ : SymState) (x : LVar) (v : Val) (not_in_ρ : ¬(x ∈ ρ.dom)) (in_σ : (x, val v) ∈ σ.toList) (noDups : σ.noDups) : List.find? (fun a ↦ (!(AssocList.toList ρ).any fun x ↦ x.fst == a.fst) && decide (a.fst = x)) (AssocList.toList σ) =
  some (x, val v) := by
  simp [*] at not_in_ρ
  let s : ∀ a : (LVar × SVal), ((!(AssocList.toList ρ).any fun x ↦ x.fst == a.fst) && decide (a.fst = x))= decide (a.fst = x) := by
    intro ⟨y, v'⟩
    simp [*]
    intro y_eq_x z v'' z_in_ρ h
    rw [h] at z_in_ρ
    rw [y_eq_x] at z_in_ρ
    let n := not_in_ρ v''
    contradiction
  simp [*]
  let h := SymState.list_find_noDups σ noDups x (val v)
  simp [*, BEq.beq] at h
  simp [*]

@[simp] theorem ConcrMap.applyOnTraceElem_kindStaysSame (ρ : ConcrMap) (t : _root_.TraceElem) : (ρ.applyOnTraceElem t).isState = t.isState ∧ (ρ.applyOnTraceElem t).isEvent = t.isEvent := by
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

theorem ConcrMap.isForTr_cons (ρ : ConcrMap) (t : _root_.TraceElem) (τ : SymTrace) (hFor : ρ.isForTr (t :: τ)) : ρ.isForTr τ := by
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
          simp
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
          | val v => simp [*]
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
          simp
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
          | val v => simp [*]
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
            simp
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
            | val v => simp [*]
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
  let not_sym : ¬((x, sym) ∈ AssocList.toList σ) := by
    intro h
    let c := concr_σ sym h
    simp [*] at c
  simp [*]
  intro σ' σ'_in_ρ_τ x_in_σ'
  apply concr σ' σ'_in_ρ_τ x sym x_in_σ'
  simp [*]

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

theorem ConcrMap.applyOnTrace_allEventsSurrounded (ρ : ConcrMap) (τ : SymTrace) (hFor : ρ.isForTr τ) (es : τ.eventsSurroundedByFittingStates) (noDups : ρ.noDups) (trNoDups : τ.noDups) :
  (ρ.applyOnTrace τ).eventsSurroundedByFittingStates := by
  induction τ with
  | nil => simp [*]
  | cons t τ' ih =>
    induction t with
    | state σ =>
      simp [ConcrMap.applyOnTrace, SymTrace.eventsSurroundedByFittingStates]
      simp [ConcrMap.isForTr] at hFor ih
      simp [SymTrace.eventsSurroundedByFittingStates] at es
      simp [SymTrace.noDups] at trNoDups
      apply ih hFor.right es trNoDups.right
    | event σ1 ev σ2 =>
      simp [*] at es
      simp [*]
      apply And.intro
      case left =>
        apply And.intro
        case left =>
          intro x v x_in_ρ
          let fc := ConcrMap.list_comp_find_noDups ρ noDups x v
          simp [*] at fc
          simp [*]
        case right =>
          intro x sv x_in_σ2
          simp [*] at hFor
          let for_σ1 := hFor.left
          by_cases x_in_ρ : (∃ x_1, (x, x_1) ∈ AssocList.toList ρ)
          case pos =>
            simp [*]
          case neg =>
            simp [*]
            exists x
            induction sv with
            | sym =>
              simp [*]
              apply And.intro
              case left =>
                simp [*] at x_in_ρ
                intro x' v x'_in_ρ
                let x_in_ρ' := x_in_ρ v
                intro h
                simp [h] at x'_in_ρ
                contradiction
              case right =>
                let x_find_σ1 := es.left x sym x_in_σ2
                let ⟨c, ch⟩ := x_find_σ1
                simp [SymTrace.noDups] at trNoDups
                let x_in_σ1 := SymState.list_find_noDups σ1 trNoDups.left x sym
                let c_eq_x : c = x := by
                  apply SymState.list_find_noDups_unique σ1 trNoDups.left x c sym ch
                simp [*] at ch x_in_ρ
                simp [*] at x_in_σ1
                let for' := for_σ1.left x sym ch
                simp [*] at for'
            | val v =>
              simp [*]
              simp [*] at x_in_ρ
              let fc := ConcrMap.list_comp_find_noDups ρ noDups x v
              rw [fc]
              let x_in_ρ' := x_in_ρ v
              simp [*]
              apply And.intro
              case left =>
                intro x' v' x'_in_ρ h
                rw [h] at x'_in_ρ
                let xv'_in_ρ := x_in_ρ v'
                contradiction
              case right =>
                let x_find_σ1 := es.left x (val v) x_in_σ2
                let ⟨c, ch⟩ := x_find_σ1
                simp [SymTrace.noDups] at trNoDups
                let x_in_σ1 := SymState.list_find_noDups σ1 trNoDups.left x (val v)
                let c_eq_x : c = x := by
                  apply SymState.list_find_noDups_unique σ1 trNoDups.left x c (val v) ch
                simp [*] at ch x_in_ρ
                apply ConcrMap.applyOnState_not_in_ρ
                simp [*]
                exact ch
                exact trNoDups.left
      case right =>
        simp [ConcrMap.isForTr] at hFor ih
        simp [SymTrace.noDups] at trNoDups
        apply ih hFor.right.right es.right trNoDups.right.right

-- Prop. 2.12.
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
        simp at hWF
        let h1 := ConcrMap.applyOnTrace_allEventsSurrounded ρ τ hFor hWF.right.right hNoDups noDups
        simp [*] at h1
        simp [*]
  case right =>
    intro σ σ_in_ρ_τ x sv x_in_σ
    let concr := ConcrMap.applyOnTr_symb_isEmpty ρ τ hFor noDups
    simp [*] at concr
    apply concr σ σ_in_ρ_τ x sv x_in_σ
