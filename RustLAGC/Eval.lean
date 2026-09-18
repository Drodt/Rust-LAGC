/-
  Work Package A3

  Based on section 3.1
-/

import Std
import Lean.Data.AssocList

import RustLAGC.Structures.Values.Basic
import RustLAGC.Structures.Traces.Basic
import RustLAGC.Structures.Rust

open Std
open Lean

open SVal
open SymTrace

open RVal
open RStmt

/--
  Local evaluation function
-/
-- TODO: Sind Listen zukunftsfähig? Besonders im Kontext unendliche Traces
-- Niklas Arbeits diesbezüglich sichten
-- Contirnuation Marker bauen
def eval (σ : SymState) (e : RExp) : List SymTrace × ContMarker := match e with
  | .v a   => ([ singleton σ ], ⟨ .v a ⟩)
  | .not a => ([ singleton σ ], ⟨ .v <| .bool false ⟩)
  | _ => sorry
