-- Traces and Events - 2.2

import Std
import Lean.Data.AssocList

import RustLAGC.Rust
import RustLAGC.LAGC.Basic

namespace SVal

-- Event markers, assuming event parameter location is irrelevant
-- TODO: Rework
-- Remark: Events festlegen, einschränken ggü. allgemeiner Definition aus Paper
/--
  Inductive type of event markers
-/
structure EvMarker where
  ev  ::
  var : List Var
  val : List SVal -- TODO: Exclude sym

-- Symbolic trace - Definition 2.1
-- Splitting the construction of trace may be sensible (also a bit of a constraint)
/--
  Construction of symbolic traces
-/
inductive SymTrace where
  | ε    : SymTrace
  | tS   : SymTrace → SymState → SymTrace 
  | tE   : SymTrace → EvMarker → SymTrace


open SymTrace
open EvMarker

/--
  Singleton trace
-/
def single (s : SymState) := tS ε s

-- Empty trace
#check ε

-- TODO: Example
-- Relevant für Continuation Marker. Kommt auf die Lean-Implemenation an
/--
  Concatenation of two symbolic traces
-/
def concat (a b : SymTrace) : SymTrace := sorry

/--
  Symbolic chop; stitching together two traces
-/
def chop (a b : SymTrace) : SymTrace := sorry

-- Concretization Mapping
def concrete (x : Var) : SVal := sorry

-- Trace Concretization
-- def concrete (x : Var) : SVal := sorry

-- TODO: Einige neue Propositions in der neuen Form
-- Well-Formed and Shining Trace - Definition 2.2
-- TODO: Definitions for use in proofs?
inductive varSym : Prop
inductive evSym  : Prop
inductive exten  : Prop

