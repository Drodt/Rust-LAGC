import RustLAGC.Data.AssocList
import RustLAGC.Structures.Value.Basic
import RustLAGC.Structures.Value.Lemmas
import RustLAGC.Structures.State.Basic

@[simp] theorem SymState.isConcrete_empty (σ : SymState) (h : σ = AssocList.nil) : σ.isConcrete := by
  simp [SymState.isConcrete, SymState.symb]
  have hl : σ.toList = [] := by simp [*]
  simp [*]

@[simp] theorem SymState.find_noDups (σ : SymState) (noDups : σ.noDups) (x : LVar) (sv : SVal) : (σ.find? x = some sv) ↔ ((x, sv) ∈ σ.toList) := by
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

theorem SymState.list_find_noDups (σ : SymState) (noDups : σ.noDups) (x : LVar) (sv : SVal) : (σ.toList.find? (fun y => y.fst == x) = some (x, sv)) ↔ ((x, sv) ∈ σ.toList) := by
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

theorem SymState.list_find_noDups_unique (σ : SymState) (noDups : σ.noDups) (x y : LVar) (sv : SVal) (h : σ.toList.find? (fun y => y.fst == x) = some (y, sv)) : y = x := by
  induction σ with
  | nil => simp [*] at h
  | cons x' sv' σ' ih =>
    simp [*] at h
    by_cases x_eq_x' : x = x'
    case pos =>
      simp [*] at h
      simp [*]
    case neg =>
      let x'_neq_x : ¬(x' = x) := by grind only
      simp [*] at h noDups
      apply ih noDups.right h

open SVal

@[simp] theorem SymState.inSymb_inDom (σ : SymState) (x : LVar) (h : x ∈ σ.symb) : x ∈ σ.dom := by
  simp [*] at h
  simp [*]
  exists sym

@[simp] theorem SymState.inSymb_isSym (σ : SymState) (x : LVar) (h : x ∈ σ.symb) : (x, sym) ∈ σ.toList := by
  simp [*] at h
  exact h

-- Prop. 3.21
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
