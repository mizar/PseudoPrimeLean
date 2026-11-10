/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaConvolution

/-! # Algebraic bounds for the even Gamma tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For the later even Gamma poles, the first paired terms in the convolution
expansion dominate the baseline. The assumptions are the paper's lower bounds
on the logarithmic scale and the pole parameter. -/
theorem quarter_gamma_tail_first {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    10 * c ^ 2 ≤ z * (27 / 25 : ℝ) * (c ^ 2 - (27 / 25 : ℝ) ^ 2) := by
  have hc2 : (25 / 4 : ℝ) ≤ c ^ 2 := by nlinarith only [hc, sq_nonneg (c - 5 / 2)]
  have hh : 0 ≤ (27 / 25 : ℝ) * (c ^ 2 - (27 / 25 : ℝ) ^ 2) := by nlinarith only [hc2]
  have hm := mul_nonneg (sub_nonneg.mpr hz) hh
  nlinarith only [hc2, hm]

/-- The scale and pole bounds also control both remaining pairs of terms in
the convolution expansion. -/
theorem quarter_gamma_tail_scale {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    3 ≤ z * (c - 27 / 25) := by
  have hm := mul_nonneg (sub_nonneg.mpr hz) (show 0 ≤ c - (27 / 25 : ℝ) by linarith only [hc])
  nlinarith only [hc, hm]

/-- The factored first-pair correction in the Gamma convolution expansion is
nonnegative for all later poles. This supplies the sign needed when its
integral expansion is inserted into the Gamma-tail comparison. -/
theorem quarter_gamma_tail_correction {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    0 ≤
      2 * (27 / 25 : ℝ) * (z * (27 / 25 : ℝ) * (c ^ 2 - (27 / 25 : ℝ) ^ 2) - 10 * c ^ 2) /
        (z * c * (c - 27 / 25) ^ 2 * (c + 27 / 25) ^ 2) := by
  have hz0 : 0 < z := by linarith only [hz]
  have hc0 : 0 < c := by linarith only [hc]
  have hnum := quarter_gamma_tail_first hz hc
  apply div_nonneg
  · nlinarith only [hnum]
  · positivity

/-- The order-two/three and order-four/five pairs on the negative side of
the convolution are nonnegative. The common scale inequality controls both
fractions, so no finite pole range is required. -/
theorem quarter_gamma_tail_remaining {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    0 ≤ 20 / (z ^ 2 * (c - 27 / 25) ^ 3) * (1 - 3 / (z * (c - 27 / 25))) ∧
      0 ≤ 120 / (z ^ 4 * (c - 27 / 25) ^ 5) * (1 - 1 / (z * (c - 27 / 25))) := by
  have hz0 : 0 < z := by linarith only [hz]
  have hc0 : 0 < c - (27 / 25 : ℝ) := by linarith only [hc]
  have hscale := quarter_gamma_tail_scale hz hc
  have hden : 0 < z * (c - (27 / 25 : ℝ)) := mul_pos hz0 hc0
  have h3 : 3 / (z * (c - (27 / 25 : ℝ))) ≤ 1 := (div_le_one hden).2 hscale
  have h1 : 1 / (z * (c - (27 / 25 : ℝ))) ≤ 1 := (div_le_one hden).2 (by linarith only [hscale])
  constructor
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr h3)
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr h1)

/-- The negative-side order-two through order-five terms in the finite
convolution expansion are nonnegative after grouping adjacent terms. -/
theorem quarter_gamma_tail_high_terms {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    0 ≤
      20 / z ^ 2 / (c - 27 / 25) ^ 3 - 60 / z ^ 3 / (c - 27 / 25) ^ 4 +
        (120 / z ^ 4 / (c - 27 / 25) ^ 5 - 120 / z ^ 5 / (c - 27 / 25) ^ 6) := by
  have h := quarter_gamma_tail_remaining hz hc
  have heq1 :
    20 / z ^ 2 / (c - 27 / 25) ^ 3 - 60 / z ^ 3 / (c - 27 / 25) ^ 4 =
      20 / (z ^ 2 * (c - 27 / 25) ^ 3) * (1 - 3 / (z * (c - 27 / 25))) := by
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring
  have heq2 :
    120 / z ^ 4 / (c - 27 / 25) ^ 5 - 120 / z ^ 5 / (c - 27 / 25) ^ 6 =
      120 / (z ^ 4 * (c - 27 / 25) ^ 5) * (1 - 1 / (z * (c - 27 / 25))) := by
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    ring
  rw [heq1, heq2]
  exact add_nonneg h.1 h.2

/-- An expansion bounded below by the baseline, the factored first-pair
correction, the grouped higher negative-side terms and a nonnegative remainder
dominates the baseline. This is the algebraic interface for the convolution
integral and avoids assuming the sign separately for each later pole. -/
theorem quarter_gamma_tail_of_expansion {z c R Q : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c)
    (hQ : 0 ≤ Q)
    (hR :
      2 / c +
          2 * (27 / 25 : ℝ) * (z * (27 / 25 : ℝ) * (c ^ 2 - (27 / 25 : ℝ) ^ 2) - 10 * c ^ 2) /
            (z * c * (c - 27 / 25) ^ 2 * (c + 27 / 25) ^ 2) +
          (20 / z ^ 2 / (c - 27 / 25) ^ 3 - 60 / z ^ 3 / (c - 27 / 25) ^ 4 +
            (120 / z ^ 4 / (c - 27 / 25) ^ 5 - 120 / z ^ 5 / (c - 27 / 25) ^ 6)) +
          Q ≤
        R) :
    2 / c ≤ R := by
  have h1 := quarter_gamma_tail_correction hz hc
  have h2 := quarter_gamma_tail_high_terms hz hc
  linarith only [h1, h2, hQ, hR]

end PseudoPrime.PrimeTestBounds.MillerRabin
