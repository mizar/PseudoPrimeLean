/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCheck
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-! # Reuse checked Euler rows for arithmetic boundary quantities -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked row encloses the actual logarithm of its prime base. Extract
the Taylor-log condition from the same Boolean certificate. This reuses
Euler row data for the Chebyshev boundary terms of the finite center. -/
theorem checked_row_log_bounds {r : EulerCenterRow} (h : eulerCenterRowCheck r = true) :
    (r.lo : ℝ) ≤ Real.log r.p ∧ Real.log r.p ≤ (r.hi : ℝ) := by
  obtain ⟨h, _⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨_, hl⟩ := Bool.and_eq_true_iff.mp h
  have hb := Analysis.rationalLogIntervalCheck_sound hl
  simpa only [Rat.cast_natCast] using hb

/-- At a checked prime-power row, the actual Mangoldt value equals the
logarithm of its prime base. Use certified primality and the positive
exponent. This connects the row payload to Chebyshev and weighted sums. -/
theorem checked_row_mangoldt_eq_log {r : EulerCenterRow} (h : eulerCenterRowCheck r = true) :
    ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)) = Real.log r.p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero r.k),
    ArithmeticFunction.vonMangoldt_apply_prime (eulerCenterRowCheck_sound h).1]

/-- At a checked prime-power row, a lower logarithm bound for the cutoff
and a nonnegative retained logarithmic factor give a lower bound for the
actual weighted Mangoldt term. Use the row's lower and upper log endpoints,
the exact prime-power Mangoldt value and the logarithm power identity.
This supplies certified boundary sums for the finite Euler center. -/
theorem checked_row_weighted_log_lower {r : EulerCenterRow} (h : eulerCenterRowCheck r = true)
    {x C : ℝ} (hx : 0 < x) (hC : C ≤ Real.log x) (hb : 0 ≤ C - ((r.k + 1 : ℕ) : ℝ) * r.hi) :
    (r.lo : ℝ) * (C - ((r.k + 1 : ℕ) : ℝ) * r.hi) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm x (r.p ^ (r.k + 1)) := by
  have hp := (eulerCenterRowCheck_sound h).1
  have hl := checked_row_log_bounds h
  have hdiff := sub_le_sub hC (mul_le_mul_of_nonneg_left hl.2 (Nat.cast_nonneg (r.k + 1)))
  have hm := mul_le_mul hl.1 hdiff hb (Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le))
  unfold AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
  rw [checked_row_mangoldt_eq_log h, Nat.cast_pow,
    Real.log_div hx.ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)), Real.log_pow]
  exact hm

end PseudoPrime.PrimeTestBounds.MillerRabin
