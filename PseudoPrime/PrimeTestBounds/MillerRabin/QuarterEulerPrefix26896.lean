/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMomentEnvelope

/-! # Analytic Euler-prefix lower bound through 26896 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An outward rational lower envelope for the first three Euler moment
increments through 26896. The positive upper-end correction is omitted. -/
noncomputable def quarterEulerMomentCert26896 (k : ℕ) : ℝ :=
  quarterEulerMomentEnvelope k (5099867 / 500000) (269641 / 100000000)

/-- The rational envelope bounds the exact moment increment from below.
This uses checked logarithm and power endpoints and the nonnegative omitted term. -/
theorem quarter_euler_moment_cert26896 (k : ℕ) :
    quarterEulerMomentCert26896 k ≤ quarterEulerMomentLower k 26896 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 26896 15 32 0 (5099867 / 500000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 26896 0 (269641 / 100000000) 29
              50 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 26896 ≤ (5099867 / 500000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (26896 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ (269641 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  exact quarter_euler_moment_envelope k (by norm_num only) hlog hpow

/-- Under RH, the Euler prefix at every cutoff at least 26896 is at least
2.902. The finite table through 1000 is reused and the rest is bounded by Abel summation. -/
theorem quarter_euler_prefix_26896_strong (hRH : RiemannHypothesis) {X : ℝ} (hX : 26896 ≤ X) :
    (1451 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h0 := quarter_euler_moment_cert26896 0
  have h1 := quarter_euler_moment_cert26896 1
  have h2 := quarter_euler_moment_cert26896 2
  have hc :
    (1451 / 500 : ℝ) ≤
      (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 + (3 / 8 : ℝ) * quarterEulerMomentCert26896 0 +
        (81 / 200 : ℝ) * quarterEulerMomentCert26896 1 +
        (729 / 5000 : ℝ) * quarterEulerMomentCert26896 2 := by
    norm_num only [quarterEulerMomentCert26896, quarterEulerMomentEnvelope,
      Analysis.logPowerTailPoly]
  have hp := quarter_euler_prefix_from_increment hRH (b := 26896) (by norm_num only)
  norm_num only [Nat.floor_ofNat] at hp
  have hl :
    (1451 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 26896, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    linarith only [h0, h1, h2, hc, hp]
  have hsub : Finset.Ioc 0 26896 ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
    intro n hn
    exact
      Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans (Nat.le_floor hX)⟩
  have hnonneg :
    ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      n ∉ Finset.Ioc 0 26896 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n _ _
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hl.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg)

/-- The preceding stronger Euler-prefix bound also supplies the earlier
2.869 threshold used by the already certified cells. -/
theorem quarter_euler_prefix_26896 (hRH : RiemannHypothesis) {X : ℝ} (hX : 26896 ≤ X) :
    (2869 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  exact
    (show (2869 / 1000 : ℝ) ≤ 1451 / 500 by norm_num only).trans
      (quarter_euler_prefix_26896_strong hRH hX)

end PseudoPrime.PrimeTestBounds.MillerRabin
