/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMomentEnvelope

/-! # Analytic Euler-prefix lower bound through 15625 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An outward rational lower envelope for the first three Euler moment
increments through 15625. The positive upper-end correction is omitted. -/
noncomputable def quarterEulerMomentCert (k : ℕ) : ℝ :=
  quarterEulerMomentEnvelope k (9656629 / 1000000) (369477 / 100000000)

/-- The rational envelope bounds the exact moment increment from below.
This uses checked logarithm and power endpoints and the nonnegative omitted term. -/
theorem quarter_euler_moment_cert (k : ℕ) :
    quarterEulerMomentCert k ≤ quarterEulerMomentLower k 15625 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 15625 14 32 0 (9656629 / 1000000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 15625 0 (369477 / 100000000) 29
              50 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 15625 ≤ (9656629 / 1000000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (15625 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ (369477 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  exact quarter_euler_moment_envelope k (by norm_num only) hlog hpow

/-- Under RH, the Euler prefix at every cutoff at least 15625 is at least
2.836. The finite table through 1000 is reused and the rest is bounded by Abel summation. -/
theorem quarter_euler_prefix_15625 (hRH : RiemannHypothesis) {X : ℝ} (hX : 15625 ≤ X) :
    (709 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h0 := quarter_euler_moment_cert 0
  have h1 := quarter_euler_moment_cert 1
  have h2 := quarter_euler_moment_cert 2
  have hc :
    (709 / 250 : ℝ) ≤
      (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 + (3 / 8 : ℝ) * quarterEulerMomentCert 0 +
        (81 / 200 : ℝ) * quarterEulerMomentCert 1 +
        (729 / 5000 : ℝ) * quarterEulerMomentCert 2 := by
    norm_num only [quarterEulerMomentCert, quarterEulerMomentEnvelope, Analysis.logPowerTailPoly]
  have hp := quarter_euler_prefix_from_increment hRH (b := 15625) (by norm_num only)
  norm_num only [Nat.floor_ofNat] at hp
  have hl :
    (709 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 15625, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    linarith only [h0, h1, h2, hc, hp]
  have hsub : Finset.Ioc 0 15625 ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
    intro n hn
    exact
      Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans (Nat.le_floor hX)⟩
  have hnonneg :
    ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      n ∉ Finset.Ioc 0 15625 → 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n _ _
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hl.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg)

end PseudoPrime.PrimeTestBounds.MillerRabin
