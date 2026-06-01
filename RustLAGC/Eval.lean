/-
  Work Package A3

  Based on section 3.1
-/

import Std
import Lean.Data.AssocList

import RustLAGC.Structures.Values
import RustLAGC.Structures.Traces
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
def eval (σ : SymState := AssocList.nil) (e : RExp) : List SymTrace × ContMarker := match e with
  | .v a   => ([ singleton σ ], ⟨ .v a ⟩)
  | .not a => ([ singleton σ ], ⟨ .v <| .bool false ⟩)
  | _ => sorry
