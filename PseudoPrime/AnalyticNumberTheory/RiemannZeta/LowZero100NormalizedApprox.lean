/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalNormalizedSign
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEM8

/-! # Finite approximation to the normalized critical-line zeta value -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The real part of the four-correction finite zeta approximation rotated
by the elementary Gamma phase. Endpoint arithmetic certifies its sign, and
the analytic approximation theorem transfers that sign to zeta. -/
@[expose]
noncomputable def normalizedFiniteEM8 (t : ℝ) : ℝ :=
  (Complex.exp ((backlundThetaMain t : ℂ) * Complex.I) * finiteEM8 t).re

/-- For `0 ≤ t ≤ 100`, rotating the finite zeta approximation does not
increase its `1/5000000` error. The rotation has norm one, and the real part
of a complex number is bounded in absolute value by its norm. -/
theorem abs_normalized_zeta_sub_em8_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    |RiemannXi.normalizedZeta t - normalizedFiniteEM8 t| ≤ 1 / 5000000 := by
  have h := norm_zeta_sub_finiteEM8_le t ht0 ht
  have h0 :=
    Complex.abs_re_le_norm
      (Complex.exp ((backlundThetaMain t : ℂ) * Complex.I) *
        (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - finiteEM8 t))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] at h0
  simp only [mul_sub, Complex.sub_re] at h0
  exact h0.trans h

/-- At `14 ≤ t ≤ 100`, a finite rotated approximation above the analytic
error budget proves that the real critical xi value is negative. -/
theorem xi_neg_of_finite_em8 {t : ℝ} (ht : 14 ≤ t) (ht100 : t ≤ 100)
    (h : 1 / 5000000 < normalizedFiniteEM8 t) :
    (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hh := abs_le.mp (abs_normalized_zeta_sub_em8_le t ht0 ht100)
  apply (RiemannXi.normalized_zeta_xi_sign ht).1
  linarith only [hh.1, h]

/-- At `14 ≤ t ≤ 100`, a finite rotated approximation below the negative
analytic error budget proves that the real critical xi value is positive. -/
theorem xi_pos_of_finite_em8 {t : ℝ} (ht : 14 ≤ t) (ht100 : t ≤ 100)
    (h : normalizedFiniteEM8 t < -(1 / 5000000 : ℝ)) :
    0 < (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hh := abs_le.mp (abs_normalized_zeta_sub_em8_le t ht0 ht100)
  apply (RiemannXi.normalized_zeta_xi_sign ht).2
  linarith only [hh.2, h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
