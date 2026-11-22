/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100NormalizedApprox

/-! # Normalized cutoff-512 Euler–Maclaurin approximation -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The real part of the cutoff-512 finite EM8 expression after rotation by the elementary
Gamma phase at height `t`. Endpoint certificates bound this real number to establish the sign
of the normalized critical-line zeta value. -/
noncomputable def normalizedFiniteEM8At512 (t : ℝ) : ℝ :=
  (Complex.exp ((backlundThetaMain t : ℂ) * Complex.I) * finiteEM8At 512 t).re

/-- At every height between zero and 500, the normalized cutoff-512 finite expression differs
from normalized critical-line zeta by less than `1 / 400000`. The existing EM8 remainder bound,
the unit norm of the rotation, and the real-part norm bound establish this analytic interface. -/
theorem abs_normalized_sub_em8_512_lt (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 500) :
    |RiemannXi.normalizedZeta t - normalizedFiniteEM8At512 t| < 1 / 400000 := by
  have h := norm_zeta_sub_em8_512_lt t ht0 ht
  have h0 :=
    Complex.abs_re_le_norm
      (Complex.exp ((backlundThetaMain t : ℂ) * Complex.I) *
        (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - finiteEM8At 512 t))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] at h0
  simp only [mul_sub, Complex.sub_re] at h0
  exact h0.trans_lt h

/-- A normalized finite EM8 value at least `1 / 8000` implies that normalized zeta exceeds
`49 / 400000` at heights between zero and 500. The analytic remainder provides the strict
margin needed by a positive endpoint certificate. -/
theorem normalized_pos_of_em8_512 (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 500)
    (h : (1 / 8000 : ℝ) ≤ normalizedFiniteEM8At512 t) :
    (49 / 400000 : ℝ) < RiemannXi.normalizedZeta t := by
  have he := (abs_lt.mp (abs_normalized_sub_em8_512_lt t ht0 ht)).1
  linarith only [he, h]

/-- A normalized finite EM8 value at most `-1 / 8000` implies that normalized zeta is below
`-49 / 400000` at heights between zero and 500. The analytic remainder provides the strict
margin needed by a negative endpoint certificate. -/
theorem normalized_neg_of_em8_512 (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 500)
    (h : normalizedFiniteEM8At512 t ≤ -(1 / 8000 : ℝ)) :
    RiemannXi.normalizedZeta t < -(49 / 400000 : ℝ) := by
  have he := (abs_lt.mp (abs_normalized_sub_em8_512_lt t ht0 ht)).2
  linarith only [he, h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
