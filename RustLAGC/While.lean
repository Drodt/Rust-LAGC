-- This file demos the formalisation of WHILE in a LAGC semantic
-- Based on Din et al., 2024

import Std
import Lean.Data.AssocList

-- Identifier 
abbrev Var := String

inductive Val where
  | tt
  | ff
  | n  : Nat → Val
deriving instance BEq, Repr for Val

inductive Op where
  | eq
  | le
  | gr
  | leq
  | geq
  | add
  | sub
  | mul
  | div
deriving instance BEq, Repr for Op

inductive SExp where
  | sym : SExp
  | var : Var → SExp
  | val : Val → SExp
  | op  : SExp → Op → SExp → SExp
deriving instance BEq, Repr for SExp

open Std
open Lean
open SExp

-- Symbolic state
-- WARNING: Does not habe a deduplication mechanic
abbrev State := AssocList Var SExp

-- Update of state
def update (σ: State) (u: Var × SExp) : State := match σ with
  | .nil         => σ.insert u.fst u.snd
  | .cons x y xs => sorry

-- Symbolic variables
-- TODO: That does not feel like writing proper Lean code
def symb (σ : State) : List Var := (σ.toList.filter fun x => x.snd == sym).map fun x => x.fst

-- Domain
def domain (σ : State) : List Var := σ.toList.map fun x => x.fst

-- Evaluation
def eval (σ : State) (statement : SExp) : SExp := match statement with
  | sym      => sym
  | var x    => if (σ.find? x) == some sym then var x else sorry
  | val x    => val x
  | op x o y => sorry

section ExampleWhile

inductive While where
  | skip   : While
  | assign : Var → SExp → While
  | ife    : SExp → While → While
  | conc   : While → While → While
  | while  : SExp → While → While
deriving Repr

open While

end ExampleWhile
