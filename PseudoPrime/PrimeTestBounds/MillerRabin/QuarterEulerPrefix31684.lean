/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMomentEnvelope

/-! # Analytic Euler-prefix lower bound through 31684 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An outward rational lower envelope for the first three Euler moment
increments through 31684. The positive upper-end correction is omitted. -/
noncomputable def quarterEulerMomentCert31684 (k : ℕ) : ℝ :=
  quarterEulerMomentEnvelope k (10363569 / 1000000) (122599 / 50000000)

/-- The rational envelope bounds the exact moment increment from below.
This uses checked logarithm and power endpoints and the nonnegative omitted term. -/
theorem quarter_euler_moment_cert31684 (k : ℕ) :
    quarterEulerMomentCert31684 k ≤ quarterEulerMomentLower k 31684 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 31684 15 32 0 (10363569 / 1000000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 31684 0 (122599 / 50000000) 29
              50 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 31684 ≤ (10363569 / 1000000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (31684 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ (122599 / 50000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  exact quarter_euler_moment_envelope k (by norm_num only) hlog hpow

/-- Under RH, the Euler prefix at every cutoff at least 31684 is at least
2.91. The finite table through 1000 is reused and the rest is bounded by Abel summation. -/
theorem quarter_euler_prefix_31684 (hRH : RiemannHypothesis) {X : ℝ} (hX : 31684 ≤ X) :
    (291 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h0 := quarter_euler_moment_cert31684 0
  have h1 := quarter_euler_moment_cert31684 1
  have h2 := quarter_euler_moment_cert31684 2
  have hc :
    (291 / 100 : ℝ) ≤
      (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 + (3 / 8 : ℝ) * quarterEulerMomentCert31684 0 +
        (81 / 200 : ℝ) * quarterEulerMomentCert31684 1 +
        (729 / 5000 : ℝ) * quarterEulerMomentCert31684 2 := by
    norm_num only [quarterEulerMomentCert31684, quarterEulerMomentEnvelope,
      Analysis.logPowerTailPoly]
  have hp := quarter_euler_prefix_from_increment hRH (b := 31684) (by norm_num only)
  norm_num only [Nat.floor_ofNat] at hp
  have hl :
    (291 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 31684, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    linarith only [h0, h1, h2, hc, hp]
  have hsub : Finset.Ioc 0 31684 ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
    intro n hn
    exact
      Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans (Nat.le_floor hX)⟩
  have hnonneg :
    ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      n ∉ Finset.Ioc 0 31684 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n _ _
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hl.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg)

end PseudoPrime.PrimeTestBounds.MillerRabin
