/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiQuarterBridge

/-! # Signed cutoff boundary for the quarter-square bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A negative signed Chebyshev lower bound at the squared radius gives a
lower bound for the cutoff boundary, using the left endpoint of the radius interval. -/
theorem quarter_bridge_boundary_lower {r l M : ℝ} (hl : 0 < l) (hr : l ≤ r) (hM : 0 ≤ M)
    (hψ : -M ≤ Chebyshev.psi (r ^ 2) - r ^ 2) :
    -(4 * M * 0.09319732 / l) ≤
      4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) := by
  have hr₀ := hl.trans_le hr
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hr₀), Real.sqrt_sq hr₀.le]
  have hw := quarter_unit_weight_656
  have hw₀ : 0 ≤ (quarterKernel656.transform 1).re := by linarith only [hw.1]
  have hunit : (quarterKernel656.transform 1).re ≤ 0.09319732 := by linarith only [hw.2]
  have hc := div_le_div_of_nonneg_right hunit hr₀.le
  have hd := div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319732) hl hr
  have hm := mul_le_mul_of_nonpos_left (hc.trans hd) (neg_nonpos.mpr hM)
  have he := mul_le_mul_of_nonneg_right hψ (div_nonneg hw₀ hr₀.le)
  calc
    -(4 * M * 0.09319732 / l) = 4 * (-M * (0.09319732 / l)) := by ring
    _ ≤ 4 * ((Chebyshev.psi (r ^ 2) - r ^ 2) * ((quarterKernel656.transform 1).re / r)) :=
      mul_le_mul_of_nonneg_left (hm.trans he) (by norm_num only)
    _ = _ := by ring

/-- On the first bridge interval, the signed Chebyshev certificate can
charge at most 0.096204 to the cutoff boundary. -/
theorem quarter_bridge_boundary_658 {r : ℝ} (hr : r ∈ Set.Icc 328 329) :
    -0.096204 ≤ 4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_quarter_bridge_658 (x := r ^ 2)
      (by nlinarith only [hr.1]) (by nlinarith only [hr.1, hr.2])
  exact
    (by norm_num only : (-0.096204 : ℝ) ≤ -(4 * 84.645 * 0.09319732 / 328)).trans
      (quarter_bridge_boundary_lower (by norm_num only) hr.1 (by norm_num only) hψ)

/-- On the second bridge interval, the signed Chebyshev certificate can
charge at most 0.100726 to the cutoff boundary. -/
theorem quarter_bridge_boundary_660 {r : ℝ} (hr : r ∈ Set.Icc 329 330) :
    -0.100726 ≤ 4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_quarter_bridge_660 (x := r ^ 2)
      (by nlinarith only [hr.1]) (by nlinarith only [hr.1, hr.2])
  exact
    (by norm_num only : (-0.100726 : ℝ) ≤ -(4 * 88.894 * 0.09319732 / 329)).trans
      (quarter_bridge_boundary_lower (by norm_num only) hr.1 (by norm_num only) hψ)

/-- On the third bridge interval, the signed Chebyshev certificate can
charge at most 0.058413 to the cutoff boundary. -/
theorem quarter_bridge_boundary_663 {r : ℝ} (hr : r ∈ Set.Icc 330 (663 / 2)) :
    -0.058413 ≤ 4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_quarter_bridge_663 (x := r ^ 2)
      (by nlinarith only [hr.1]) (by nlinarith only [hr.1, hr.2])
  exact
    (by norm_num only : (-0.058413 : ℝ) ≤ -(4 * 51.708 * 0.09319732 / 330)).trans
      (quarter_bridge_boundary_lower (by norm_num only) hr.1 (by norm_num only) hψ)

end PseudoPrime.PrimeTestBounds.MillerRabin
