/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCombinedLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiNarrow
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredNumerics

/-! # Narrow combined centered principal bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The narrow relative-window cost separates exactly into square-root and
inverse-square-root terms at positive radii. -/
theorem quarter_narrow_window_cost {r : ℝ} (hr : 0 < r) :
    let h := (3 / 7 : ℝ) / Real.sqrt r
    (h / (59 / 30) * r ^ 2 + (231 / 2500 : ℝ) / h * r + (231 / 2500 : ℝ) / h) / r =
      ((30 / 59 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
        (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  dsimp only
  field_simp (disch :=
    first
    | exact hr.ne'
    | exact hs.ne'
    | norm_num only)
  rw [Real.sq_sqrt hr.le]
  ring

/-- Under RH, radii at least 180 have an improved combined principal-sum
lower bound. The narrow Chebyshev window and combined variation bounds give
the explicit `529/5000`, `7/200`, and `351/200` error coefficients. -/
theorem quarter_combined_centered_numeric (hRH : RiemannHypothesis) {r : ℝ} (hr : 180 ≤ r) :
    (27 / 25 : ℝ) ^ 5 *
          ((24439 / 50000 : ℝ) * r - (529 / 5000 : ℝ) * Real.sqrt r - (7 / 200 : ℝ) -
            (351 / 200 : ℝ) / r -
            (526064 / 10000000 : ℝ) / Real.sqrt r) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hw := refined_unit_weight_centered
  have hd := refined_unit_deriv_centered
  have hc1 :
    4 * refinedWeight 1 * ((30 / 59 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) ≤
      (27 / 25 : ℝ) ^ 5 * (529 / 5000) := by
    norm_num only at ⊢
    linarith only [hw]
  have hc2 :
    4 * refinedWeight 1 * ((231 / 2500 : ℝ) * (7 / 3)) ≤
      (27 / 25 : ℝ) ^ 5 * (526064 / 10000000) := by
    norm_num only at ⊢
    linarith only [hw]
  have hw1 := mul_le_mul_of_nonneg_right hc1 hs.le
  have hw2 := mul_le_mul_of_nonneg_right hc2 (inv_nonneg.mpr hs.le)
  have hwin :
    4 * refinedWeight 1 *
        ((((3 / 7 : ℝ) / Real.sqrt r) / (59 / 30) * r ^ 2 +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r)) /
          r) ≤
      (27 / 25 : ℝ) ^ 5 *
        ((529 / 5000 : ℝ) * Real.sqrt r + (526064 / 10000000 : ℝ) / Real.sqrt r) := by
    rw [quarter_narrow_window_cost hr0]
    ring_nf at hw1 hw2 ⊢
    linarith only [hw1, hw2]
  have hcV :
    3 * ((203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) - 2 * (179 / 1000 : ℝ) + 4 * |refinedWeightDeriv 1| ≤
      (7 / 10 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    norm_num only at ⊢
    linarith only [hd]
  have hcN :
    (21 / 20 : ℝ) * (3 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) + 2 * |refinedWeightDeriv 1|) ≤
      (351 / 200 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    norm_num only at ⊢
    linarith only [hd]
  have hV := mul_le_mul_of_nonneg_left hcV (show (0 : ℝ) ≤ (1 / 20 : ℝ) * r by positivity)
  have hother :
    ((1 / 20 : ℝ) * r *
            (3 * ((203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) - 2 * (179 / 1000 : ℝ) +
              4 * |refinedWeightDeriv 1|) +
          (21 / 20 : ℝ) *
            (3 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) + 2 * |refinedWeightDeriv 1|)) /
        r ≤
      (27 / 25 : ℝ) ^ 5 * ((7 / 200 : ℝ) + (351 / 200 : ℝ) / r) := by
    apply (div_le_iff₀ hr0).mpr
    field_simp (disch := exact hr0.ne')
    nlinarith only [hV, hcN]
  have hpsi := quarter_psi_narrow hRH hr
  have hmul :=
    mul_le_mul_of_nonneg_left hpsi
      (show (0 : ℝ) ≤ 4 * refinedWeight 1 by
        exact mul_nonneg (by norm_num only) refined_unit_weight_nonneg)
  have hnum :
    -(4 * refinedWeight 1 *
          (((3 / 7 : ℝ) / Real.sqrt r) / (59 / 30) * r ^ 2 +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r))) ≤
      4 * refinedWeight 1 * (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) := by
    nlinarith only [hmul]
  have hdiv := div_le_div_of_nonneg_right hnum hr0.le
  have hmain := mul_le_mul_of_nonneg_right refined_paper_delta_lower.le hr0.le
  rw [← refined_unit_main_eq] at hmain
  have h := quarter_combined_centered_lower hRH hr2
  simp only [Real.sqrt_sq hr0.le] at h
  simp only [add_div, sub_div, neg_div] at h hdiv ⊢
  ring_nf at hwin hother hmain h hdiv ⊢
  linarith only [hwin, hother, hmain, h, hdiv]

end PseudoPrime.PrimeTestBounds.MillerRabin
