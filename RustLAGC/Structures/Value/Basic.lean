/-
  Work Package A2

  Based on section 2
-/

import Std
import ExtendedDeriveDecEq
import RustLAGC.Data.AssocList

open Std
open Lean

/--
  Def. 2.1. Type of variables in LAGC. Abbreviation of type String.
-/
abbrev LVar : Type := String

/--
  Def. 2.1. Type of places
-/
inductive Place where
  | pV : LVar  → Place          -- Var
  | pN : Place → Nat   → Place          -- Arrays
  | pI : Place → String → Place -- Structs
deriving instance BEq, DecidableEq, Repr for Place

/--
  Def. 2.1. Type of borrow identifiers
-/
inductive BId where
  | mk : LVar → BId
deriving instance BEq, DecidableEq, ReflBEq, LawfulBEq, Repr for BId

mutual
/--
  Def. 2.1. Type of starred values
-/
inductive Val where
  | b      : Bool  → Val       -- Mapping Lean types directly to SVal
  | z      : Int   → Val
  | refS   : Place → BId → Val -- Shared reference
  | refM   : Place → BId → Val -- Mutable reference
  | tuple  : List Val  → Val
  | arr    : List Val → Val
 -- ignore struct, enum, fn right now
end

derive_deceq Val

deriving instance Repr for Val

-- Example 2.2
#check Val.tuple [Val.b True, Val.z 8, Val.refM (Place.pV "n") (BId.mk "0")]

-- Def. 2.1.
inductive SVal where
| sym :  SVal               -- Equivalent to *
| val : Val -> SVal

deriving instance Repr, DecidableEq for SVal


-- Def. 3.19
structure Renaming where
  var : LVar -> LVar
  varInv : LVar -> LVar
  borrow : BId -> BId
  borrowInv : BId → BId

namespace Renaming

@[simp] def bijective (r : Renaming) : Prop :=
  (∀ (x y : LVar), r.var x = r.var y -> x = y)
  ∧ (∀ (y : LVar), ∃ (x : LVar), r.var x = y)
  ∧ (∀ (x y : BId), r.borrow x = r.borrow y -> x = y)
  ∧ (∀ (y : BId), ∃ (x : BId), r.borrow x = y)
  ∧ (∀ (x : LVar), r.varInv (r.var x) = x)
  ∧ (∀ x : BId, r.borrowInv (r.borrow x) = x)

@[simp] def inv (r : Renaming) : Renaming := .mk r.varInv r.var r.borrowInv r.borrow

@[simp] def compose (r1 r2 : Renaming) : Renaming := .mk (fun x => r2.var (r1.var x)) (fun x => r1.varInv (r2.varInv x)) (fun x => r2.borrow (r1.borrow x)) (fun x => r1.borrowInv (r2.borrowInv x))

end Renaming

@[simp] def Place.rename (p : Place) (κ : LVar -> LVar) : Place := match p with
| .pV x => .pV (κ x)
| .pN p' n => .pN (p'.rename κ) n
| .pI p' f => .pI (p'.rename κ) f

@[simp] def Val.rename : Val -> Renaming -> Val
| .tuple vs, r => .tuple (vs.map (fun v' => v'.rename r))
| .arr vs, r => .arr (vs.map (fun v' => v'.rename r))
-- | .struct s fs, r => .struct s (fs.map (fun f => ⟨ f.fst, f.snd.rename r ⟩))
| .refS p bid, r => .refS (p.rename r.var) (r.borrow bid)
| .refM p bid, r => .refM (p.rename r.var) (r.borrow bid)
| v, _ => v

@[simp] def SVal.rename : SVal → Renaming → SVal
| .sym, _ => .sym
| .val v, r => .val (v.rename r)

@[simp] def renameOptVal : Option SVal → Renaming → Option SVal
| .some sv, r => .some (sv.rename r)
| .none, _ => .none
