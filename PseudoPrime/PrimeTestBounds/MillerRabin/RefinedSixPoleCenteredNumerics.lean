/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredConstants

/-! # Rational costs in the centered principal comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The relative-window cost at `r²`, divided by `r`, consists of a square-root
term and an inverse-square-root term. This is an exact identity for positive `r`. -/
theorem refined_centered_window_cost {r : ℝ} (hr : 0 < r) :
    let h := (3 / 7 : ℝ) / Real.sqrt r
    (h / (19 / 10) * r ^ 2 + (231 / 2500 : ℝ) / h * r + (231 / 2500 : ℝ) / h) / r =
      ((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt r +
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

/-- Under RH, the centered principal comparison at `r ≥ 34` has explicit
rational costs. The exact logarithmic atom is retained for the final gap test. -/
theorem refined_combined_centered_numeric (hRH : RiemannHypothesis) {r : ℝ} (hr : 34 ≤ r) :
    (27 / 25 : ℝ) ^ 5 *
          ((24439 / 50000 : ℝ) * r - (108 / 1000 : ℝ) * Real.sqrt r - (6695 / 100000 : ℝ) -
            (29757 / 10000 : ℝ) / r -
            (526064 / 10000000 : ℝ) / Real.sqrt r) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 34).trans_le hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hw := refined_unit_weight_centered
  have hd := refined_unit_deriv_centered
  have hc1 :
    4 * refinedWeight 1 * ((10 / 19 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) ≤
      (27 / 25 : ℝ) ^ 5 * (108 / 1000) := by
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
        ((((3 / 7 : ℝ) / Real.sqrt r) / (19 / 10) * r ^ 2 +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r)) /
          r) ≤
      (27 / 25 : ℝ) ^ 5 *
        ((108 / 1000 : ℝ) * Real.sqrt r + (526064 / 10000000 : ℝ) / Real.sqrt r) := by
    rw [refined_centered_window_cost hr0]
    ring_nf at hw1 hw2 ⊢
    linarith only [hw1, hw2]
  have hdr := mul_le_mul_of_nonneg_right hd hr0.le
  have hother :
    (5 *
            ((1 / 20 : ℝ) * r * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
              (21 / 20 : ℝ) * ((251 / 500) * (27 / 25 : ℝ) ^ 5)) +
          4 * |refinedWeightDeriv 1| * (r / 20 + 21 / 20)) /
        r ≤
      (27 / 25 : ℝ) ^ 5 * ((6695 / 100000 : ℝ) + (29757 / 10000 : ℝ) / r) := by
    apply (div_le_iff₀ hr0).mpr
    field_simp (disch := exact hr0.ne')
    nlinarith only [hd, hdr]
  have hmain := mul_le_mul_of_nonneg_right refined_paper_delta_lower.le hr0.le
  rw [← refined_unit_main_eq] at hmain
  have h := refined_combined_centered_scale hRH hr
  dsimp only at h
  ring_nf at hwin hother hmain h ⊢
  linarith only [hwin, hother, hmain, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
