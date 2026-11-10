/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerSmoothed

/-! # Upper smoothed Mangoldt value at 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational upper contribution to the smoothed Mangoldt sum at 1000.
The checked lower logarithm endpoint safely bounds its square. -/
def quarterSmoothUpper (n : ℕ) (r : RefinedEulerAtom) : ℚ :=
  if IsPrimePow n then r.hi * (6907756 / 1000000) - r.k * r.lo ^ 2 else 0

/-- A checked prime-power row supplies an upper bound for its smoothed
Mangoldt term at 1000. The logarithm interval and nonnegative lower endpoint
bound the two factors with the appropriate directions. -/
theorem quarter_smooth_row_upper {n : ℕ} {r : RefinedEulerAtom}
    (hc : IsPrimePow n → refinedEulerAtomCheck 24 n r = true) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm 1000 n ≤
      (quarterSmoothUpper n r : ℝ) := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [refinedEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    simp only [Rat.cast_natCast] at hl
    have hp0 : 0 ≤ Real.log r.p := Real.log_natCast_nonneg r.p
    have hlo0 : (0 : ℝ) ≤ r.lo := by exact_mod_cast h.1.2.2.2.1
    have hsq := pow_le_pow_left₀ hlo0 hl.1 2
    have hhi : (0 : ℝ) ≤ r.hi := hp0.trans hl.2
    have hU := (Analysis.rationalLogIntervalCheck_sound refined_log_1000_check).2
    norm_num only at hU
    have hmul := mul_le_mul hl.2 hU (Real.log_natCast_nonneg 1000) hhi
    have hk := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg r.k : (0 : ℝ) ≤ r.k)
    have ht :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_prime_pow
        (by norm_num only : (1000 : ℝ) ≠ 0) h.1.1 h.1.2.1
    rw [h.1.2.2.1] at ht
    simp only [quarterSmoothUpper, ite_eq_left hn, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
    rw [ht]
    nlinarith only [hmul, hk]
  · have hz :=
      AnalyticNumberTheory.Arithmetic.logMangoldtTerm_eq_zero_of_not_primePow (x := (1000 : ℝ)) hn
    simp only [quarterSmoothUpper, ite_eq_right hn, Rat.cast_zero, hz, le_refl]

end PseudoPrime.PrimeTestBounds.MillerRabin
