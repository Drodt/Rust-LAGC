import Std
import Lean.Data.AssocList

import RustLAGC.LAGC.Basic
import RustLAGC.LAGC.Traces
import RustLAGC.Rust

open Std
open Lean

open SVal
open RExp

def eval (σ : SymState := AssocList.nil) (e : RExp) : List SymTrace := sorry
