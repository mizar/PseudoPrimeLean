/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMR240Numerics
public import PseudoPrime.Analysis.GaussianMRRelativeNumerics
/-! # Fixed Gaussian cutoff 35000 with logarithmic upper endpoint 240 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The fixed Gaussian radius sqrt(87500/3), independent of the input logarithm.
Multiplication of its square by 6/5 gives the witness cutoff 35000.
It is shared by the large-index and index-four comparisons. -/
noncomputable def gaussian35000Radius : ℝ := Real.sqrt (87500 / 3 : ℝ)
/-- The positive square root of the fixed Gaussian radius.
It determines the relative width h=1/(3s). Its explicit rational bounds
control both normalization errors at the fixed cutoff. -/
noncomputable def gaussian35000Root : ℝ := Real.sqrt gaussian35000Radius

/-- The fixed radius is at least 8539/50. Compare exact squares under the square root.
This lower bound controls inverse-radius errors without a logarithmic lower threshold. -/
theorem gaussian35000_radius_lower : (8539 / 50 : ℝ) ≤ gaussian35000Radius := by
  exact Real.le_sqrt_of_sq_le (by norm_num only)

/-- The fixed fourth root lies between 13 and 131/10.
Apply the square-root comparisons to the certified radius and rational fourth powers.
These bounds supply positivity, the width condition, and the linear loss cap. -/
theorem gaussian35000_root_bounds :
    (13 : ℝ) ≤ gaussian35000Root ∧ gaussian35000Root ≤ 131 / 10 := by
  have hr := gaussian35000_radius_lower
  constructor
  · exact Real.le_sqrt_of_sq_le (by linarith only [hr])
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num only, ?_⟩
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num only, by norm_num only⟩

/-- The square of the fixed radius is exactly 87500/3.
Use the nonnegative radicand in the square-root identity.
This identifies the analytic scale and the final witness cutoff. -/
theorem gaussian35000_radius_sq : gaussian35000Radius ^ 2 = (87500 / 3 : ℝ) :=
  Real.sq_sqrt (by norm_num only)

/-- The square of the fixed root is the radius.
The radius is nonnegative because it is a square root.
This connects the fixed parameters to the relative normalization theorem. -/
theorem gaussian35000_root_sq : gaussian35000Root ^ 2 = gaussian35000Radius :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

/-- For log q<=240, the fixed-prefix ambient error is at most 539/100.
Use the common tail estimates and the rational pole cap 1771/1000.
No lower logarithmic bound is required for this error estimate. -/
theorem gaussian35000_ambient {q : ℕ} (hq : Real.log q ≤ 240) :
    LLS.PaperStatements.gaussianPrefixError (47 / 10) q (gaussian35000Radius ^ 2) ≤
      539 / 100 := by
  have hr := gaussian35000_radius_lower
  have hp : 0 < gaussian35000Radius := by linarith only [hr]
  have ht := gaussianMR6_tail240 (by linarith only [hr] : 170 ≤ gaussian35000Radius)
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / gaussian35000Radius) ≤
      1771 / 1000 := by
    rw [← mul_div_assoc, div_le_iff₀ hp]
    nlinarith only [hr, hq]
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hp.le]
  linarith only [ht.1, ht.2, hP]

/-- The inverse-root and inverse-radius loss is at most the displayed rational constant.
Use s>=13 and r>=8539/50 with positive denominators.
This estimate enters both fixed-cutoff index budgets. -/
theorem gaussian35000_T_upper :
    63 * gaussianMR6FifthsEndpoint / (10 * gaussian35000Root) +
      1839 * gaussianMR6FifthsEndpoint / (1000 * gaussian35000Radius) ≤
        (2341518909 / 4440280000 : ℝ) := by
  have hr := gaussian35000_radius_lower
  have hs := gaussian35000_root_bounds.1
  have h1 : 63 * gaussianMR6FifthsEndpoint / (10 * gaussian35000Root) ≤
      63 * gaussianMR6FifthsEndpoint / (10 * 13) := by
    apply div_le_div_of_nonneg_left (by norm_num only [gaussianMR6FifthsEndpoint])
      (by norm_num only)
    linarith only [hs]
  have h2 : 1839 * gaussianMR6FifthsEndpoint / (1000 * gaussian35000Radius) ≤
      1839 * gaussianMR6FifthsEndpoint / (1000 * (8539 / 50)) := by
    apply div_le_div_of_nonneg_left (by norm_num only [gaussianMR6FifthsEndpoint])
      (by norm_num only)
    linarith only [hr]
  dsimp only [gaussianMR6FifthsEndpoint] at h1 h2 ⊢
  linarith only [h1, h2]

/-- For L<=240 and index m>=10^9, the fixed Gaussian scalar budget is impossible
when the ambient error is at most 539/100. Bound index coefficients and inverse losses
by their rational endpoints; the remaining exact rational gap is positive. -/
theorem gaussian35000_large_absurd {L m A : ℝ} (hL : L ≤ 240)
    (hm : gaussianMR6FifthsIndex ≤ m) (hA : A ≤ 539 / 100)
    (hb : gaussianMR6FifthsD * gaussian35000Radius ≤ gaussianMR6FifthsConductor * L +
      gaussianMR6FifthsBeta * gaussian35000Root + (m / (m - 1)) *
        (63 * gaussianMR6FifthsEndpoint / (10 * gaussian35000Root) +
          1839 * gaussianMR6FifthsEndpoint / (1000 * gaussian35000Radius)) +
        13 / (m - 1) + A) : False := by
  have hcoeff := gaussianMR6Fifths_index_coefficients hm
  have hT := gaussian35000_T_upper
  have hm1 : 0 < m - 1 := by
    norm_num only [gaussianMR6FifthsIndex] at hm
    linarith only [hm]
  have ht0 : 0 ≤ m / (m - 1) := div_nonneg (by linarith only [hm1]) hm1.le
  have hscaled := mul_le_mul_of_nonneg_left hT ht0
  have hgamma := mul_le_mul_of_nonneg_right hcoeff.2.1
    (by norm_num only : (0 : ℝ) ≤ 2341518909 / 4440280000)
  have h13 : 13 / (m - 1) ≤ 13 / (gaussianMR6FifthsIndex - 1) := by
    apply div_le_div_of_nonneg_left (by norm_num only)
      (by norm_num only [gaussianMR6FifthsIndex])
    linarith only [hm]
  have hdr := mul_le_mul_of_nonneg_left gaussian35000_radius_lower
    gaussianMR6Fifths_coefficients_pos.1.le
  have hbs := mul_le_mul_of_nonneg_left gaussian35000_root_bounds.2
    gaussianMR6Fifths_coefficients_pos.2.le
  have hcL := mul_le_mul_of_nonneg_left hL
    (by norm_num only [gaussianMR6FifthsConductor] : 0 ≤ gaussianMR6FifthsConductor)
  have hgap : gaussianMR6FifthsD * (8539 / 50) > gaussianMR6FifthsConductor * 240 +
      gaussianMR6FifthsBeta * (131 / 10) +
      (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) * (2341518909 / 4440280000) +
      13 / (gaussianMR6FifthsIndex - 1) + 539 / 100 := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsConductor, gaussianMR6FifthsBeta,
      gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  linarith only [hb, hA, hscaled, hgamma, h13, hdr, hbs, hcL, hgap]

/-- For L<=240, the index-four scalar budget with conductor factor 2/3 is impossible
when the ambient error is at most 539/100. Use the fixed radius and root bounds
and the positive rational gap. This discharges the uniform Korselt triple. -/
theorem gaussian35000_four_absurd {L A : ℝ} (hL : L ≤ 240) (hA : A ≤ 539 / 100)
    (hb : ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * gaussian35000Radius ≤
      (161 / 400 : ℝ) * ((2 / 3 : ℝ) * L) +
      ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10)) * gaussian35000Root +
      (4 / 3 : ℝ) * (63 * gaussianMR6FifthsEndpoint / (10 * gaussian35000Root) +
        1839 * gaussianMR6FifthsEndpoint / (1000 * gaussian35000Radius)) + 13 / 3 + A) :
    False := by
  have hT := mul_le_mul_of_nonneg_left gaussian35000_T_upper
    (by norm_num only : (0 : ℝ) ≤ 4 / 3)
  have hdr := mul_le_mul_of_nonneg_left gaussian35000_radius_lower
    (by norm_num only [gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] :
      0 ≤ (4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3)
  have hbs := mul_le_mul_of_nonneg_left gaussian35000_root_bounds.2
    (by norm_num only [gaussianMR6FifthsMass] :
      0 ≤ (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10))
  norm_num only [gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at hb hT hdr hbs
  linarith only [hb, hA, hT, hdr, hbs, hL]

end PseudoPrime.Analysis
