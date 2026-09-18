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
deriving instance BEq, DecidableEq, Repr for Place

/--
  Type of borrow identifiers
-/
inductive BId where
  | mk : LVar → BId
deriving instance BEq, DecidableEq, ReflBEq, LawfulBEq, Repr for BId

mutual
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
end

derive_deceq Val

deriving instance Repr for Val

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

@[simp] def Renaming.compose (r1 r2 : Renaming) : Renaming := Renaming.mk (fun x => r2.var (r1.var x)) (fun x => r1.varInv (r2.varInv x)) (fun x => r2.borrow (r1.borrow x)) (fun x => r1.borrowInv (r2.borrowInv x))

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

inductive SVal where
| sym :  SVal               -- Equivalent to *
| val : Val -> SVal

deriving instance Repr, DecidableEq for SVal

@[simp] def SVal.rename : SVal → Renaming → SVal
| .sym, _ => .sym
| .val v, r => .val (v.rename r)

@[simp] def renameOptVal : Option SVal → Renaming → Option SVal
| .some sv, r => .some (sv.rename r)
| .none, _ => .none

open SVal

/--
  Symbolic state is a list of mappings Var → SVal
  Consider the usage of list-specific operations like `map` via `toList`
-/
abbrev SymState := _root_.AssocList LVar SVal

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

@[simp] def SymState.noDups : SymState -> Bool
| AssocList.nil => true
| AssocList.cons x _ σ' => ¬σ'.contains x ∧ noDups σ'

@[simp] def SymState.extends (σ1 σ2 : SymState) : Bool := σ1.all
  (fun x v => σ2.find? x == some v)

instance : BEq SymState where
  beq (σ1 σ2 : SymState) : Bool := σ1.dom == σ2.dom ∧ σ2.extends σ1

@[simp] def SymState.eqModR (σ1 σ2 : SymState) (xs : List LVar) : Prop :=
  σ1.dom.all (fun x => (x ∈ xs) -> x ∈ σ2.dom)
  ∧ σ2.dom.all (fun x => (x ∈ xs) -> x ∈ σ1.dom)
  ∧ (∀ x ∈ σ1.dom, (x ∈ xs) -> σ1.find? x = σ2.find? x)
  ∧ ∃ r : Renaming,
    r.bijective
    ∧ (∀ x ∈ σ1.dom, (¬x ∈ xs) → r.var x ∈ σ2.dom ∧ ¬(r.var x ∈ xs) ∧ σ1.find? x = renameOptVal (σ2.find? (r.var x)) r.inv)
    ∧ (∀ x ∈ σ2.dom, (¬x ∈ xs) → r.varInv x ∈ σ1.dom ∧ ¬(r.varInv x ∈ xs) ∧ σ2.find? x = renameOptVal (σ1.find? (r.varInv x)) r)
