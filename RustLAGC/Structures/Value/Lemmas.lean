import RustLAGC.Structures.Value.Basic

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

theorem Place.rename_id (p : Place) : p.rename (fun x => x) = p := by
  induction p <;> simp [*]

theorem Place.rename_inv (p : Place) (r : Renaming) (r_bij : r.bijective) : (p.rename r.var).rename r.varInv = p := by
  induction p <;> simp [*]
  case pV x =>
    simp [*] at *
    apply r_bij.right.right.right.right.left


theorem Place.rename_compose (p : Place) (r1 r2 : Renaming) : (p.rename r1.var).rename r2.var = p.rename (r1.compose r2).var := by
  simp [*]
  induction p <;> simp [*]

theorem Val.rename_id (v : Val) : v.rename (Renaming.mk (fun y => y) (fun y => y) (fun y => y) (fun y => y)) = v := by
  induction v using Val.induction <;> simp [*, Place.rename_id] <;> induction ‹List Val› with
    | nil => simp [*]
    | cons v vs' tih =>
      simp [*]
      apply tih
      intro v' v'_in_vs
      let ih' := ‹∀ (v_1 : Val), v_1 ∈ v :: vs' →
        v_1.rename { var := fun y ↦ y, varInv := fun y ↦ y, borrow := fun y ↦ y, borrowInv := fun y ↦ y } = v_1› v'
      simp [*]

theorem Val.rename_inv (v : Val) (r : Renaming) (r_bij : r.bijective) : (v.rename r).rename r.inv = v := by
  simp [*]
  induction v <;> simp [*] <;> first
  | apply And.intro
    case left =>
      apply Place.rename_inv
      exact r_bij
    case right =>
      simp [*] at r_bij
      apply r_bij.right.right.right.right.right
  | induction ‹List Val› with
    | nil => simp [*]
    | cons x xs ih' =>
      simp [*] at *
      let ih'' := ih' ‹(x.rename r).rename { var := r.varInv, varInv := r.var, borrow := r.borrowInv, borrowInv := r.borrow } = x ∧
        ∀ (a : Val),
          a ∈ xs → (a.rename r).rename { var := r.varInv, varInv := r.var, borrow := r.borrowInv, borrowInv := r.borrow } = a›.right
      exact ih''

theorem Val.rename_compose (v : Val) (r1 r2 : Renaming) : (v.rename r1).rename r2 = v.rename (r1.compose r2) := by
  simp [*]
  induction v <;> simp [*, Place.rename_compose] <;> first
  | intro v v_in_vs
    let vs := ‹List Val›
    let ih := ‹∀ (v : Val),
      v ∈ vs →
      (v.rename r1).rename r2 =
      v.rename
        { var := fun x ↦ r2.var (r1.var x), varInv := fun x ↦ r1.varInv (r2.varInv x),
          borrow := fun x ↦ r2.borrow (r1.borrow x), borrowInv := fun x ↦ r1.borrowInv (r2.borrowInv x) }›
    apply ih v v_in_vs


theorem SVal.rename_id (sv : SVal) : sv.rename (Renaming.mk (fun y => y) (fun y => y) (fun y => y) (fun y => y)) = sv := by
  induction sv <;> simp [*, Val.rename_id]
