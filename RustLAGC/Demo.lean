-- This file demos the formalisation of WHILE in a LAGC semantic
-- Based on Din et al., 2024

inductive While where
  | var    : String → While
  | val    : Type → While
  | op     : Type → Type → While
  | exp    : While
  | sexp   : While


structure SymTrace

def state (var : While): While := sorry

def update (a : While): While := sorry

def eval (a : While): SymTrace := sorry
