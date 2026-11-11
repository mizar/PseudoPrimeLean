/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCombinedLower
import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredNumerics

/-! # Combined centered bound from a one-sided Chebyshev error -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, a one-sided error bound at `r²` controls the combined principal sums.
The centered Abel estimate and explicit weight constants give a reusable lower bound. -/
theorem quarter_combined_of_psi (hRH : RiemannHypothesis) {r M : ℝ} (hr : 1 ≤ r) (hM : 0 ≤ M)
    (hpsi : -M ≤ Chebyshev.psi (r ^ 2) - r ^ 2) :
    (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - ((61 / 250 : ℝ) * M + 351 / 200) / r) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hw := refined_unit_weight_centered
  have hd := refined_unit_deriv_centered
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
  have hc : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
  have hw0 := refined_unit_weight_nonneg
  have hpsi' : -M ≤ Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi) := by
    linarith only [hpsi, hc]
  have hmul :=
    mul_le_mul_of_nonneg_left hpsi'
      (show (0 : ℝ) ≤ 4 * refinedWeight 1 by exact mul_nonneg (by norm_num only) hw0)
  have hbound : 4 * refinedWeight 1 * M ≤ (27 / 25 : ℝ) ^ 5 * ((61 / 250 : ℝ) * M) := by
    have h := mul_le_mul_of_nonneg_right hw hM
    norm_num only at h ⊢
    linarith only [h]
  have hnum :
    -((27 / 25 : ℝ) ^ 5 * ((61 / 250 : ℝ) * M)) ≤
      4 * refinedWeight 1 * (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) := by
    nlinarith only [hmul, hbound]
  have hdiv := div_le_div_of_nonneg_right hnum hr0.le
  have hmain := mul_le_mul_of_nonneg_right refined_paper_delta_lower.le hr0.le
  rw [← refined_unit_main_eq] at hmain
  have h := quarter_combined_centered_lower hRH hr2
  simp only [Real.sqrt_sq hr0.le] at h
  simp only [add_div, sub_div, neg_div] at h hdiv ⊢
  ring_nf at hother hmain h hdiv ⊢
  linarith only [hother, hmain, h, hdiv]

/-- Under RH, a lower bound `psi(r²) ≥ r² - 600` gives the explicit combined
principal-sum lower bound used by the uniform quarter-bound interval certificates. -/
theorem quarter_combined_of_psi600 (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 ≤ r)
    (hpsi : r ^ 2 - 600 ≤ Chebyshev.psi (r ^ 2)) :
    (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - (29631 / 200 : ℝ) / r) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have h :=
    quarter_combined_of_psi hRH hr (show (0 : ℝ) ≤ 600 by norm_num only)
      (show -(600 : ℝ) ≤ Chebyshev.psi (r ^ 2) - r ^ 2 by linarith only [hpsi])
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
