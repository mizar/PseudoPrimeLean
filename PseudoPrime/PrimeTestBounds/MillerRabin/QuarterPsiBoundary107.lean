/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSignedBoundary570
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiSection107
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Signed cutoff terms for the four comparisons of section 107 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the whole section 107 interval, the positive logarithmic boundary
uses the lower unit weight and the upper radius 313. -/
theorem quarter_log_boundary_107 {r : ℝ} (hr : 0 < r) (hu : r ≤ 313) :
    0.002137 ≤ 4 * quarterWeight570 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  rw [quarter_cutoff_weight_570 (sq_pos_of_pos hr), Real.sqrt_sq hr.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hw : (0.09104 : ℝ) ≤ (quarterKernel570.transform 1).re := by
    linarith only [quarter_unit_weight_570.1]
  have h := signed_boundary_pos_570 hr hu (by norm_num only : (0 : ℝ) ≤ 1.837) hlog hw
  rw [show ∀ w t : ℝ, 4 * (w / r) * t = 4 * w * t / r from fun w t ↦ by ring]
  exact (by norm_num only : (0.002137 : ℝ) ≤ 4 * 0.09104 * 1.837 / 313).trans h

/-- The signed cutoff term on radii [300,304] is bounded using the
corresponding Chebyshev error and its sign. -/
theorem quarter_psi_boundary_304 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 304) :
    4 * 0.09105 * (-89) / 300 ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_section107_first
      ((by norm_num only : (90000 : ℝ) ≤ 300 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2).trans (by norm_num only))
  exact cutoff_boundary_neg_570 (by norm_num only) hl (by norm_num only) hψ

/-- The signed cutoff term on radii [304,308] is bounded using the
corresponding Chebyshev error and its sign. -/
theorem quarter_psi_boundary_308 {r : ℝ} (hl : 304 ≤ r) (hu : r ≤ 308) :
    4 * 0.09105 * (-36) / 304 ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_section107_second
      ((by norm_num only : (92416 : ℝ) ≤ 304 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2).trans (by norm_num only))
  exact cutoff_boundary_neg_570 (by norm_num only) hl (by norm_num only) hψ

/-- The signed cutoff term on radii [308,312] is bounded using the
corresponding Chebyshev error and its sign. -/
theorem quarter_psi_boundary_312 {r : ℝ} (hl : 308 ≤ r) (hu : r ≤ 312) :
    4 * 0.09104 * 25 / 312 ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_section107_third
      ((by norm_num only : (94864 : ℝ) ≤ 308 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2).trans (by norm_num only))
  exact cutoff_boundary_pos_570 (by linarith only [hl]) hu (by norm_num only) hψ

/-- The signed cutoff term on radii [312,313] is bounded using the
corresponding Chebyshev error and its sign. -/
theorem quarter_psi_boundary_313 {r : ℝ} (hl : 312 ≤ r) (hu : r ≤ 313) :
    4 * 0.09104 * (79 / 10) / 313 ≤
      4 * quarterWeight570 (r ^ 2) (r ^ 2) * (Chebyshev.psi (r ^ 2) - r ^ 2) := by
  have hψ :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_section107_last
      ((by norm_num only : (97344 : ℝ) ≤ 312 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2).trans (by norm_num only))
  exact cutoff_boundary_pos_570 (by linarith only [hl]) hu (by norm_num only) hψ

end PseudoPrime.PrimeTestBounds.MillerRabin
