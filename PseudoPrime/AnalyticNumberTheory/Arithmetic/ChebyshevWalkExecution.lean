/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogWalkExecution
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerWitnessExecution

/-! # Sequential fixed-point execution for Chebyshev psi -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A fixed-point walk state: `n` is the current integer; `logLo` and `logHi`
bound its logarithm, and `psiLo` and `psiHi` bound its Chebyshev psi value,
all at one common natural scale. The soundness theorem states the invariants. -/
structure PsiWalkState where
  n : ℕ
  logLo : ℕ
  logHi : ℕ
  psiLo : ℕ
  psiHi : ℕ
  deriving DecidableEq

/-- The next integer is either certified non-prime-power by two coprime
factors, is prime, or is a positive power of the stated prime with supplied
fixed-point logarithm bounds. Power bounds are certified independently. -/
inductive PsiWalkEntry where
  | composite (d : ℕ)
  | prime
  | power (p k logLo logHi : ℕ)
  deriving DecidableEq

/-- Update both logarithm bounds at the next integer using outward rounding.
The remaining fields are copied until the corresponding Mangoldt term is added. -/
def psiWalkLogStep (S : ℕ) (s : PsiWalkState) : PsiWalkState :=
  { s with
    n := s.n + 1
    logLo := s.logLo + 2 * S / (2 * s.n + 1)
    logHi := s.logHi + (S / s.n + 1) }

/-- Check one next-integer certificate and update the fixed-point state.
Prime entries use the freshly advanced logarithm; prime powers use supplied
bounds. A failed arithmetic condition returns `none`. -/
def psiWalkStep (S : ℕ) (s : PsiWalkState) (e : PsiWalkEntry) : Option PsiWalkState :=
  let t := psiWalkLogStep S s
  match e with
  | .composite d => if decide (0 < d) && primePowerWitnessCheck t.n d then some t else none
  | .prime =>
    if @decide t.n.Prime (Nat.decidablePrime' t.n) then
      some
        { t with
          psiLo := t.psiLo + t.logLo, psiHi := t.psiHi + t.logHi }
    else none
  | .power p k lo hi =>
    if @decide p.Prime (Nat.decidablePrime' p) && decide (p ^ (k + 1) = t.n) then
      some
        { t with
          psiLo := t.psiLo + lo, psiHi := t.psiHi + hi }
    else none

/-- Execute a finite sequence of checked psi updates from left to right.
Each recursive call consumes one entry, so no list element is indexed. -/
def psiWalk (S : ℕ) : PsiWalkState → List PsiWalkEntry → Option PsiWalkState
  | s, [] => some s
  | s, e :: es =>
    match psiWalkStep S s e with
    | none => none
    | some t => psiWalk S t es

end PseudoPrime.AnalyticNumberTheory.Arithmetic
