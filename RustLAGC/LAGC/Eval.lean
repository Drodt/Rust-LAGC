-- Section 3.1

import Std
import Lean.Data.AssocList

import RustLAGC.LAGC.Values
import RustLAGC.LAGC.Traces
import RustLAGC.Rust

open Std
open Lean

open SVal
open SymTrace
open RExp

def eval (σ : SymState := AssocList.nil) (e : RExp) : List SymTrace := match e with
  | v a => [ tS ε σ  ]
