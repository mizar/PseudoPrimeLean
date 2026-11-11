/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripBounds

/-! # Right boundary for the pole-cancelled zeta strip estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On the line `Re s = 3/2`, the distances to `1` and `-2` satisfy the
displayed bounds. Compare the squares of their complex norms. -/
private theorem right_strip_geometry {s : ℂ} (hs : s.re = 3 / 2) :
    ‖s - 1‖ ≤ ‖s + 2‖ ∧ (7 / 2 : ℝ) ≤ ‖s + 2‖ := by
  have h1 := Complex.sq_norm (s - 1)
  have h2 := Complex.sq_norm (s + 2)
  rw [Complex.normSq_apply] at h1 h2
  have hre : (2 : ℂ).re = 2 := rfl
  have him : (2 : ℂ).im = 0 := rfl
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, hre, him, sub_zero, add_zero] at h1 h2
  have hA : ‖s - 1‖ ≤ ‖s + 2‖ := by
    nlinarith only [h1, h2, hs, norm_nonneg (s - 1), norm_nonneg (s + 2)]
  have hB : (7 / 2 : ℝ) ≤ ‖s + 2‖ := by nlinarith only [h2, hs, norm_nonneg (s + 2), sq_nonneg s.im]
  exact ⟨hA, hB⟩

/-- On the line `Re s = 3/2`, the pole-cancelled auxiliary function
`riemannZeta₁ s / (s + 2)^2` has norm at most `4/5`. The right half-plane
Dirichlet-series bound and the distance to `-2` give the stated constant. -/
theorem norm_zeta_strip_right {s : ℂ} (hs : s.re = 3 / 2) :
    ‖riemannZeta₁ s / (s + 2) ^ 2‖ ≤ (4 / 5 : ℝ) := by
  have hne : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num only [Complex.one_re] at hs
  have hzeq : riemannZeta₁ s = (s - 1) * riemannZeta s :=
    ((eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.mpr hne)).mp (riemannZeta_eq_inv_sub_mul hne)).symm
  have hA := (right_strip_geometry hs).1
  have hB := (right_strip_geometry hs).2
  have hz := norm_zeta_lt_fourteen_fifths hs.ge
  have hb0 : 0 < ‖s + 2‖ := by linarith only [hB]
  have hp : 0 < ‖s + 2‖ ^ 2 := pow_pos hb0 _
  have hm : ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s + 2‖ * (14 / 5 : ℝ) :=
    mul_le_mul hA hz.le (norm_nonneg _) (norm_nonneg _)
  rw [hzeq, norm_div, norm_mul, norm_pow]
  apply (div_le_iff₀ hp).2
  nlinarith only [hm, hB, sq_nonneg (‖s + 2‖ - 7 / 2)]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
