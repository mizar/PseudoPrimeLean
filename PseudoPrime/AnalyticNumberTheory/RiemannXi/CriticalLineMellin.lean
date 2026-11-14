/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros

/-! # Critical-line xi signs and the regularized Mellin transform -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The real part of the regularized completed zeta function at height `t`
on the critical line. It is the analytic quantity to bound when certifying
endpoint signs of the xi function. -/
noncomputable def criticalCompletedZeta (t : ℝ) : ℝ :=
  (completedRiemannZeta₀ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re

/-- On the critical line, the real xi value is a real affine expression in
`criticalCompletedZeta`. The identity follows from the regularized xi
formula and eliminates complex Gamma factors from the sign test. -/
theorem xi_critical_re_eq (t : ℝ) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re =
      1 / 2 - (t ^ 2 + 1 / 4) * criticalCompletedZeta t / 2 := by
  dsimp only [riemannXi, criticalCompletedZeta]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hhalf]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
  ring

/-- A critical-line xi value is positive exactly when the corresponding
regularized completed-zeta value is below the explicit algebraic threshold.
This form avoids dividing by a computed interval bound. -/
theorem xi_critical_pos_iff (t : ℝ) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ↔
      (t ^ 2 + 1 / 4) * criticalCompletedZeta t < 1 := by
  rw [xi_critical_re_eq]
  constructor <;> intro h <;> linarith only [h]

/-- A critical-line xi value is negative exactly when the corresponding
regularized completed-zeta value is above the explicit algebraic threshold. -/
theorem xi_critical_neg_iff (t : ℝ) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 ↔
      1 < (t ^ 2 + 1 / 4) * criticalCompletedZeta t := by
  rw [xi_critical_re_eq]
  constructor <;> intro h <;> linarith only [h]

/-- The regularized completed zeta is the Mellin transform of mathlib's
modified even theta kernel, with the conventional factor of one half.
The formula holds at every complex argument, including the critical line. -/
theorem completed_zeta_zero_eq_mellin (s : ℂ) :
    completedRiemannZeta₀ s = mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) / 2 := by rfl

/-- The modified theta-kernel Mellin integral converges absolutely at every
complex argument. In particular it can be truncated at a critical-line
endpoint once an explicit tail bound has been supplied. -/
theorem completed_zeta_mellin_convergent (s : ℂ) :
    MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) := by
  exact ((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1

/-- Above one, the modified kernel in the regularized completed-zeta
integral is the even theta kernel with its constant term removed. -/
theorem modified_theta_kernel_above_one {x : ℝ} (hx : 1 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x = (HurwitzZeta.evenKernel 0 x : ℂ) - 1 := by
  simp only [WeakFEPair.f_modif, Pi.add_apply,
    Set.indicator_of_mem (show x ∈ Set.Ioi (1 : ℝ) from hx),
    Set.indicator_of_notMem (show x ∉ Set.Ioo (0 : ℝ) 1 from fun h ↦ (not_lt_of_ge hx.le) h.2),
    add_zero, HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, ite_true]

/-- The nonconstant even theta kernel is the absolutely summable Gaussian
series over nonzero integers. It supplies a computable expansion for the
kernel in the critical-line Mellin representation. -/
theorem theta_kernel_gaussian_sum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else Real.exp (-Real.pi * (n : ℝ) ^ 2 * x))
      (HurwitzZeta.evenKernel 0 x - 1) := by
  simpa only [add_zero, Int.cast_eq_zero, AddCircle.coe_zero, ite_true] using
    HurwitzZeta.hasSum_int_evenKernel₀ 0 hx

end PseudoPrime.AnalyticNumberTheory.RiemannXi
