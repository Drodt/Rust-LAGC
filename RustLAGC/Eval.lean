/-
  Work Package A3

  Based on section 3.1
-/

import Std
import Lean.Data.AssocList

import RustLAGC.Structures.Values
import RustLAGC.Structures.Traces
import RustLAGC.Rust

open Std
open Lean

open SVal
open SymTrace
open RStmt

/--
  Local evaluation function
-/
-- TODO: Sind Listen zukunftsfähig? Besonders im Kontext unendliche Traces
-- NIklas Arbeits diesbezüglich sichten
-- Contirnuation marker bauen
def eval (σ : SymState := AssocList.nil) (e : RExp) : List SymTrace := match e with
  | .v a   => [ single σ ]
  | .not a => [ single σ ]
  | _ => sorry
