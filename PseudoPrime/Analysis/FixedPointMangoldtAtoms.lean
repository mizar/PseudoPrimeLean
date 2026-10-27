/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FixedPointExponentialIntervals
public import PseudoPrime.Analysis.FixedPointLogIntervals
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-! # Certified natural fixed-point exponential Mangoldt atoms -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The natural lower scaled exponential Mangoldt atom at index n and
scale A/B. Use the certified logarithm of minFac(n), reciprocal exponential lower
bound and downward product rounding on prime powers; return zero elsewhere. -/
def mangoldtExpFixedLower (n A B scale logSteps expSteps : ℕ) : ℕ :=
  if IsPrimePow n then
    expNegFixedLower (n * B) A scale expSteps *
        logFixedLower (n.minFac : ℚ) (n.minFac.log2 + 1) logSteps scale /
      scale
  else 0

/-- The natural upper scaled exponential Mangoldt atom at index n and
scale A/B. Multiply upward logarithm and exponential bounds and round up.
Non-prime-power indices return zero, matching the Mangoldt support exactly. -/
def mangoldtExpFixedUpper (n A B scale logSteps expSteps : ℕ) : ℕ :=
  if IsPrimePow n then
    let u :=
      logFixedUpper (n.minFac : ℚ) (n.minFac.log2 + 1) logSteps scale *
        expNegFixedUpper (n * B) A scale expSteps
    (u + scale - 1) / scale
  else 0

/-- For positive A and scale, valid prime-power logarithm checks and the
Taylor size condition, the computed atom bounds scale*exp(-n*B/A)*Lambda(n) below.
Use the exact Mangoldt formula and downward product rounding. -/
theorem mangoldtExpFixedLower_le (n A B scale logSteps expSteps : ℕ) (hA : 0 < A) (hs : 0 < scale)
    (hc : IsPrimePow n → logFixedCheck (n.minFac : ℚ) (n.minFac.log2 + 1) logSteps = true)
    (hsize : (((n * B : ℕ) : ℝ) / A) / (expSteps + 1 : ℕ) ≤ 1 / 2) :
    (mangoldtExpFixedLower n A B scale logSteps expSteps : ℝ) ≤
      (scale : ℝ) * (Real.exp (-((n * B : ℕ) : ℝ) / A) * ArithmeticFunction.vonMangoldt n) := by
  by_cases hn : IsPrimePow n
  · rw [mangoldtExpFixedLower, ite_eq_left hn, ArithmeticFunction.vonMangoldt_apply, ite_eq_left hn]
    have hl := (logFixed_bounds (scale := scale) (hc hn)).1
    simp only [Rat.cast_natCast] at hl
    exact
      fixedPoint_mul_lower hs (Real.exp_pos _).le
        (expNegFixedLower_le (n * B) A scale expSteps hA hs hsize) hl
  · rw [mangoldtExpFixedLower, ite_eq_right hn, Nat.cast_zero,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, mul_zero, mul_zero]

/-- For positive scale and exponential term count, valid prime-power
logarithm checks make the computed atom an upper bound for the actual scaled atom.
Use the exact Mangoldt support and upward product rounding. -/
theorem mangoldtExpFixedUpper_ge (n A B scale logSteps expSteps : ℕ) (hs : 0 < scale)
    (he : 0 < expSteps)
    (hc : IsPrimePow n → logFixedCheck (n.minFac : ℚ) (n.minFac.log2 + 1) logSteps = true) :
    (scale : ℝ) * (Real.exp (-((n * B : ℕ) : ℝ) / A) * ArithmeticFunction.vonMangoldt n) ≤
      (mangoldtExpFixedUpper n A B scale logSteps expSteps : ℝ) := by
  by_cases hn : IsPrimePow n
  · rw [mangoldtExpFixedUpper, ite_eq_left hn, ArithmeticFunction.vonMangoldt_apply, ite_eq_left hn]
    have hl := (logFixed_bounds (scale := scale) (hc hn)).2
    simp only [Rat.cast_natCast] at hl
    have h :=
      fixedPoint_mul_upper hs (Real.exp_pos _).le hl
        (expNegFixedUpper_ge (n * B) A scale expSteps hs he)
    simpa only [mul_comm] using h
  · rw [mangoldtExpFixedUpper, ite_eq_right hn, Nat.cast_zero,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, mul_zero, mul_zero]

end PseudoPrime.Analysis
