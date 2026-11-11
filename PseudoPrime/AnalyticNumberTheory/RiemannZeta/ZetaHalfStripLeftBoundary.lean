/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripLeft
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripBounds

/-! # Left boundary for the pole-cancelled zeta strip estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `Re s = -1/2`, both the distance to `1` and the norm of `s` are at
most the distance to `-2`. Compare the squares of the complex norms. -/
private theorem left_strip_geometry {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖s - 1‖ ≤ ‖s + 2‖ ∧ ‖s‖ ≤ ‖s + 2‖ := by
  have h0 := Complex.sq_norm s
  have h1 := Complex.sq_norm (s - 1)
  have h2 := Complex.sq_norm (s + 2)
  rw [Complex.normSq_apply] at h0 h1 h2
  have hre : (2 : ℂ).re = 2 := rfl
  have him : (2 : ℂ).im = 0 := rfl
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, hre, him, sub_zero, add_zero] at h1 h2
  have hA : ‖s - 1‖ ≤ ‖s + 2‖ := by
    nlinarith only [h1, h2, hs, norm_nonneg (s - 1), norm_nonneg (s + 2)]
  have hB : ‖s‖ ≤ ‖s + 2‖ := by nlinarith only [h0, h2, hs, norm_nonneg s, norm_nonneg (s + 2)]
  exact ⟨hA, hB⟩

/-- On `Re s = -1/2`, the pole-cancelled auxiliary function
`riemannZeta₁ s / (s + 2)^2` has norm at most `4/5`. Reflect zeta to the
right boundary and use the explicit half-plane norm bound. -/
theorem norm_zeta_strip_left {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖riemannZeta₁ s / (s + 2) ^ 2‖ ≤ (4 / 5 : ℝ) := by
  have hne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    norm_num only at hs
  have hzeq : riemannZeta₁ s = (s - 1) * riemannZeta s :=
    ((eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.mpr hne)).mp (riemannZeta_eq_inv_sub_mul hne)).symm
  have hA := (left_strip_geometry hs).1
  have hB := (left_strip_geometry hs).2
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hscale : (14 / 5 : ℝ) / (2 * Real.pi) ≤ 4 / 5 := by
    apply (div_le_iff₀ hpi).2
    linarith only [Real.pi_gt_three]
  have hz1 : ‖riemannZeta (1 - s)‖ < (14 / 5 : ℝ) := by
    apply norm_zeta_lt_fourteen_fifths
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hs_bound : ‖riemannZeta s‖ ≤ (4 / 5 : ℝ) * ‖s‖ := by
    rw [norm_zeta_left_reflection hs]
    calc
      ‖s‖ / (2 * Real.pi) * ‖riemannZeta (1 - s)‖ ≤ ‖s‖ / (2 * Real.pi) * (14 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hz1.le (div_nonneg (norm_nonneg s) hpi.le)
      _ = ((14 / 5 : ℝ) / (2 * Real.pi)) * ‖s‖ := by ring
      _ ≤ (4 / 5 : ℝ) * ‖s‖ := mul_le_mul_of_nonneg_right hscale (norm_nonneg s)
  have hB0 : 0 < ‖s + 2‖ := by
    have hsne : s + 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have ht : (2 : ℂ).re = 2 := rfl
      simp only [Complex.add_re, Complex.zero_re, ht] at hre
      linarith only [hs, hre]
    exact norm_pos_iff.mpr hsne
  have hprod := mul_le_mul hA hs_bound (norm_nonneg _) (norm_nonneg (s + 2))
  have hscaleB := mul_le_mul_of_nonneg_left hB (norm_nonneg (s + 2))
  rw [hzeq, norm_div, norm_mul, norm_pow]
  apply (div_le_iff₀ (pow_pos hB0 _)).2
  nlinarith only [hprod, hscaleB]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
