/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkExecution

/-! # Integer crossing guards for fixed-point psi walk blocks -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Check the two square-root endpoint guards and both crossing inequalities
for a block whose start and final psi states use scale `S`. The envelope
candidates `ca` and `cb` use scale 1000. All checks are natural arithmetic. -/
def psiWalkBlockGuard (S : ℕ) (s t : PsiWalkState) (ca cb : ℕ) : Bool :=
  decide
    (0 < S ∧
      25 * ca ^ 2 ≤ 16000000 * s.n ∧
      25 * cb ^ 2 ≤ 16000000 * (t.n + 1) ∧
      1000 * S * (t.n + 1) ≤ 1000 * s.psiLo + S * cb ∧ 1000 * t.psiHi ≤ 1000 * S * s.n + S * ca)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
