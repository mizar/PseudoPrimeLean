/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpNormalForm
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFinitePointwise
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianNormalAbsorption
public import PseudoPrime.Analysis.GaussianSeededSharpMonotone
public import PseudoPrime.Analysis.GaussianLowSwitches

/-! # Monotonicity of the public sharp envelopes in the plotting range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- In the regular plotting range, the sharp selection is at least 23.
Its normal form combines a finite pointwise floor with larger Gaussian
and seeded floors. This controls the connection from the small-input branch. -/
theorem sharpSelected_floor23 {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 30000000000) :
    (23 : ℝ) ≤ sharpSelectedEnvelope n := by
  rw [sharpSelected_eq_regular hN hU]
  apply le_min (lowFinitePointwise_floor23 _)
  apply le_min
  · have h := gaussianLowFamily_floor (Real.log n)
    linarith only [h]
  · have h := Analysis.gaussianSeededSharp_floor (Real.log n)
    linarith only [h]

/-- The logarithm of 3000 is below the first strengthened finite-principal
cap. Compare 3000 with 3 times 2^10 and use certified logarithm constants. -/
theorem log3000_lt_firstFiniteCap : Real.log (3000 : ℝ) < (8087 / 1000 : ℝ) := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (by norm_num only : (3000 : ℝ) ≤ 3 * 2 ^ 10)
  rw [Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- At the small-input boundary 3000 the public selected value is exactly 23.
The regular lower bound and the active first finite guard give both inequalities. -/
theorem sharpSelected_at3000 : sharpSelectedEnvelope 3000 = (23 : ℝ) := by
  have hU : Real.log (3000 : ℝ) < 30000000000 := by linarith only [log3000_lt_firstFiniteCap]
  apply le_antisymm
  · rw [sharpSelected_eq_regular (le_refl 3000) hU]
    apply (min_le_left _ _).trans
    exact
      lowFinitePointwise_le_profile .p23
        (by
          simpa only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat,
            Nat.cast_ofNat] using log3000_lt_firstFiniteCap.le)
  · exact sharpSelected_floor23 (le_refl 3000) hU

/-- Prime rounding preserves the exact value 23 at the boundary 3000. -/
theorem sharpPrime_at3000 : sharpPrimeEnvelope 3000 = (23 : ℝ) := by
  change primeRound (sharpWitnessEnvelope 3000) = (23 : ℝ)
  rw [sharp_eq_selected (by decide : 1 < 3000), sharpSelected_at3000]
  exact primeRound_prime (by decide : Nat.Prime 23)

/-- For 9<=m<=n and log n below thirty billion, the public sharp selection
is nondecreasing. The regular range is a finite minimum of monotone functions
of log n. The small branches connect in order 2, 3, and then at least 23. -/
theorem sharpSelected_mono_normal {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : sharpSelectedEnvelope m ≤ sharpSelectedEnvelope n := by
  by_cases hnsmall : n < 3000
  · by_cases hn2 : n < 2047
    · rw [sharpSelected_small_two (lt_of_le_of_lt hmn hn2), sharpSelected_small_two hn2]
    · rw [sharpSelected_small_three (le_of_not_gt hn2) hnsmall]
      by_cases hm2 : m < 2047
      · rw [sharpSelected_small_two hm2]
        norm_num only
      · rw [sharpSelected_small_three (le_of_not_gt hm2) (lt_of_le_of_lt hmn hnsmall)]
  · have hnlarge : 3000 ≤ n := le_of_not_gt hnsmall
    by_cases hmsmall : m < 3000
    · have hfloor := sharpSelected_floor23 hnlarge hU
      by_cases hm2 : m < 2047
      · rw [sharpSelected_small_two hm2]
        linarith only [hfloor]
      · rw [sharpSelected_small_three (le_of_not_gt hm2) hmsmall]
        linarith only [hfloor]
    · have hmlarge : 3000 ≤ m := le_of_not_gt hmsmall
      have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 9) hm
      have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hm1)) (Nat.cast_le.mpr hmn)
      rw [sharpSelected_eq_regular hmlarge (hlog.trans_lt hU), sharpSelected_eq_regular hnlarge hU]
      exact
        min_le_min (lowFinitePointwise_mono hlog)
          (min_le_min (Analysis.gaussianLowFamily_mono hlog)
            (Analysis.gaussianSeededSharp_mono hlog))

/-- Prime rounding preserves the public selection's monotonicity on the
same natural-input range. Rewrite the analytic cutoff to its selection and
apply monotonicity of the total greatest-prime rounding function. -/
theorem sharpPrime_mono_normal {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : sharpPrimeEnvelope m ≤ sharpPrimeEnvelope n := by
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 9) hm
  have hn1 : 1 < n := hm1.trans_le hmn
  change primeRound (sharpWitnessEnvelope m) ≤ primeRound (sharpWitnessEnvelope n)
  rw [sharp_eq_selected hm1, sharp_eq_selected hn1]
  exact primeRound_mono (sharpSelected_mono_normal hm hmn hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
