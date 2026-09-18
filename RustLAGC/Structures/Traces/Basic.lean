/-
  Work Package A2

  Based on section 2
-/

import Std

import RustLAGC.Data.AssocList
import RustLAGC.Structures.Values.Basic
import RustLAGC.Structures.Values.Lemmas
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

deriving instance BEq for _root_.TraceElem
deriving instance Inhabited for _root_.TraceElem

@[simp] def TraceElem.isState : _root_.TraceElem -> Bool
| TraceElem.state _ => true
| _ => false

@[simp] def TraceElem.isEvent : _root_.TraceElem -> Bool
| TraceElem.event _ _ _=> true
| _ => false

/--
  Construction of symbolic traces
-/
abbrev SymTrace := List _root_.TraceElem

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

abbrev ConcrMap := _root_.AssocList LVar Val

@[simp] def ConcrMap.dom (ρ : ConcrMap) : List LVar := ρ.toList.map fun x => x.fst

@[simp] def ConcrMap.noDups : ConcrMap -> Bool
| .nil => true
| .cons x _ ρ' => ¬ρ'.contains x ∧ noDups ρ'

@[simp] def ConcrMap.isFor (ρ : ConcrMap) (σ : SymState) : Bool :=
  σ.symb.all (fun X => ρ.contains X)
  /\ σ.dom.all (fun x => ρ.contains x == (σ.find? x == some SVal.sym))

@[simp] def ConcrMap.toState (ρ : ConcrMap) : SymState := ρ.mapVal (fun _ v => (SVal.val v))

@[simp] def ConcrMap.applyOnState (ρ : ConcrMap) (σ : SymState) : SymState :=
  (ρ.toState.toList ++ (σ.toList.filter (fun (x, _) => ¬ρ.contains x))).toAssocList

def ρ₀ : ConcrMap := [("X", Val.z 3)].toAssocList
#eval ConcrMap.applyOnState ρ₀ σ₀

@[simp] def ConcrMap.applyOnEvent (ρ : ConcrMap) (ev : EventMarker) : EventMarker :=
  (.mk ev.1
      (ev.2.map (fun e => match e with
        | EvPar.var x => if let some v := ρ.find? x
            then EvPar.val v
            else e
        | EvPar.val _ => e
        )))

@[simp] def ConcrMap.applyOnTraceElem (ρ : ConcrMap) (te : _root_.TraceElem) : _root_.TraceElem := match te with
| TraceElem.state σ => TraceElem.state (ConcrMap.applyOnState ρ σ)
| TraceElem.event σ1 ev σ2 => TraceElem.event (ρ.applyOnState σ1) (ρ.applyOnEvent ev) (ρ.applyOnState σ2)

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
