/-
  Work Package A2

  Based on section 2
-/

import Std
import Lean.Data.AssocList

import RustLAGC.Structures.Values
import RustLAGC.Structures.Rust

namespace SVal

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
  | val : SVal → EvPar

/--
  Inductive type of event markers
-/
inductive EventMarker where
  | mk : String → List EvPar → EventMarker

/--
  Construction of symbolic traces
-/
inductive SymTrace where
  | ε    : SymTrace
  | tS   : SymTrace → SymState → SymTrace 
  | tE   : SymTrace → EventMarker → SymTrace

open SymTrace
open EventMarker

/--
  Singleton trace
-/
def SymTrace.singleton (s : SymState) := tS ε s


/-
  Concatenation of two symbolic traces
-/
def concat (a b : SymTrace) : SymTrace := match a, b with
  | _ , ε            => a
  | ε , _            => b
  | tS x j , tS y k  => ε
  | _ , _            => ε

/-
  Symbolic chop; stitching together two traces
-/
-- def chop (a b : SymTrace) : SymTrace := match a, b with
--   | _ , _ => sorry

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
def σ₀: SymState := .mk [("X", sym), ("y", b false)]
#check ((singleton σ₀).tE ⟨ "ev₀", [EvPar.var "X"]⟩).tS (σ₀.updateVar ("y", b true))

-- Other examples
-- Empty trace
#check ε
-- Construction without dot-notation
#check tS (tE (tS ε <| .mk []) ⟨"inv", []⟩) <| .mk []
-- Example 2.3: Construction with dot-notation
#check (((singleton <| .mk []).tE ⟨"ev₀", [EvPar.var "v"]⟩).tS <| .mk [] ).tS <| .mk [("X", sym)]
