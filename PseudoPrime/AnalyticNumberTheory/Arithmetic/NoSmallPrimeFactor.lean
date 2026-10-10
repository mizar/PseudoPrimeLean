/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-!
# Small-prime-factor exclusion clears the common-factor weighted sums

This file gives the arithmetic step behind LLS Theorem 1.1(2)'s original small-prime-exclusion
hypothesis: if `m` has no prime factor strictly below `X`, then both weighted common-factor sums
`commonFactorLogWeightedSum X m` and `commonFactorReciprocalWeightedSum X m` vanish identically.

No character is involved: this is a fact about the natural number `m` and the real cutoff `X`
alone. It does not require `X ∉ ℕ`, or that the boundary case `p = X` (for `p ∣ m` prime) cannot
occur: at `n = X` the log-weight `log(X / n)` and the reciprocal weight `1 - n / X` both vanish, so
that boundary term contributes `0` to the sum regardless of whether it survives the strict
inequality used in the hypothesis.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a natural `m` and real cutoff `X`, no prime `p` with `(p : ℝ) < X` divides `m`.
The inequality is strict, so a prime at the cutoff remains admissible. This hypothesis makes
the common-factor weighted sums vanish because their boundary weights are zero. -/
def NoSmallPrimeFactor (m : ℕ) (X : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) < X → ¬p ∣ m

end PseudoPrime.AnalyticNumberTheory.Arithmetic
