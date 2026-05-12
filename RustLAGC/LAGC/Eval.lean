/-
  Work Package A3

  Based on section 3.1
-/

import Std
import Lean.Data.AssocList

import RustLAGC.LAGC.Values
import RustLAGC.LAGC.Traces
import RustLAGC.Rust

open Std
open Lean

open SVal
open SymTrace
open RStmt

/--
  Local evaluation function
-/
def eval (σ : SymState := AssocList.nil) (e : RStmt) : List SymTrace := match e with
  | .mk $ .v a   => [ single σ ]
  | .mk $ .not a => [ single σ ]
  | _ => sorry
