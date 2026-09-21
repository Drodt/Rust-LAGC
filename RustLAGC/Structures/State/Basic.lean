import RustLAGC.Data.AssocList
import RustLAGC.Structures.Value.Basic

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

-- Def. 2.3
@[simp] def SymState.extends (σ1 σ2 : SymState) : Bool := σ1.all
  (fun x v => σ2.find? x == some v)

instance : BEq SymState where
  beq (σ1 σ2 : SymState) : Bool := σ1.dom == σ2.dom ∧ σ2.extends σ1

-- Def. 3.20
@[simp] def SymState.eqModR (σ1 σ2 : SymState) (xs : List LVar) : Prop :=
  σ1.dom.all (fun x => (x ∈ xs) -> x ∈ σ2.dom)
  ∧ σ2.dom.all (fun x => (x ∈ xs) -> x ∈ σ1.dom)
  ∧ (∀ x ∈ σ1.dom, (x ∈ xs) -> σ1.find? x = σ2.find? x)
  ∧ ∃ r : Renaming,
    r.bijective
    ∧ (∀ x ∈ σ1.dom, (¬x ∈ xs) → r.var x ∈ σ2.dom ∧ ¬(r.var x ∈ xs) ∧ σ1.find? x = renameOptVal (σ2.find? (r.var x)) r.inv)
    ∧ (∀ x ∈ σ2.dom, (¬x ∈ xs) → r.varInv x ∈ σ1.dom ∧ ¬(r.varInv x ∈ xs) ∧ σ2.find? x = renameOptVal (σ1.find? (r.varInv x)) r)
