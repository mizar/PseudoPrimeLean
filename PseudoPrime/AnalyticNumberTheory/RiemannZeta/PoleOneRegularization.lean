/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Meromorphic.LogDeriv
public import Mathlib.Tactic

/-! # Kernel-independent zeta PoleOneRegularization -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The factor removing the logarithmic derivative's pole at one, extended using `riemannZeta₁`. -/
noncomputable def riemannZetaOneLogDerivativeRegularization (s : ℂ) : ℂ :=
  1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s)

/-- Near one, multiplying the negative zeta logarithmic derivative by `s-1` gives its extension. -/
theorem eventuallyEq_riemannZetaOneLogDerivativeRegularization :
    Filter.EventuallyEq (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ))
      (fun s : ℂ ↦ (s - 1) * (-(deriv riemannZeta s / riemannZeta s)))
      riemannZetaOneLogDerivativeRegularization := by
  filter_upwards [eventually_mem_nhdsWithin, log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs
    hslog
  rw [riemannZetaOneLogDerivativeRegularization, hslog]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)
  calc
    (s - 1) * -(-(s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s) =
        (s - 1) * (s - 1)⁻¹ - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s) :=
      by ring
    _ = 1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s) := by rw [mul_inv_cancel₀ hsub]

/-- The regularized negative logarithmic derivative is differentiable at one. -/
theorem differentiableAt_riemannZetaOneLogDerivativeRegularization :
    DifferentiableAt ℂ riemannZetaOneLogDerivativeRegularization 1 := by
  have hzetaOne : riemannZeta₁ 1 ≠ 0 := by
    simp only [riemannZeta₁_one, ne_eq, one_ne_zero, not_false_eq_true]
  unfold riemannZetaOneLogDerivativeRegularization
  fun_prop (disch := assumption)

/-- The regularized negative logarithmic derivative is analytic near one. -/
theorem analyticAt_riemannZetaOneLogDerivativeRegularization :
    AnalyticAt ℂ riemannZetaOneLogDerivativeRegularization 1 := by
  have hzetaOne : riemannZeta₁ 1 ≠ 0 := by
    simp only [riemannZeta₁_one, ne_eq, one_ne_zero, not_false_eq_true]
  have hquotient : AnalyticAt ℂ (fun s ↦ deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    (differentiable_riemannZeta₁.analyticAt 1).deriv.div (differentiable_riemannZeta₁.analyticAt 1)
      hzetaOne
  unfold riemannZetaOneLogDerivativeRegularization
  fun_prop

/-- The regularized negative logarithmic derivative has value one at one. -/
theorem riemannZetaOneLogDerivativeRegularization_one :
    riemannZetaOneLogDerivativeRegularization 1 = 1 := by
  simp only [riemannZetaOneLogDerivativeRegularization, sub_self, deriv_riemannZeta₁_one,
    riemannZeta₁_one, div_one, zero_mul, sub_zero]

/-- The derivative of the regularized negative zeta logarithmic derivative at one is `-γ`. -/
theorem deriv_riemannZetaOneLogDerivativeRegularization_one :
    deriv riemannZetaOneLogDerivativeRegularization 1 = -Real.eulerMascheroniConstant := by
  have hzetaOne : riemannZeta₁ 1 ≠ 0 := by
    simp only [riemannZeta₁_one, ne_eq, one_ne_zero, not_false_eq_true]
  have hquotient : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta₁ s / riemannZeta₁ s) 1 := by
    exact
      (differentiable_riemannZeta₁.analyticAt 1).deriv.differentiableAt.div
        differentiable_riemannZeta₁.differentiableAt hzetaOne
  unfold riemannZetaOneLogDerivativeRegularization
  rw [deriv_const_sub, deriv_fun_mul (by fun_prop) hquotient]
  simp only [differentiableAt_fun_id, differentiableAt_const, deriv_fun_sub, deriv_id'',
    deriv_const', sub_zero, deriv_riemannZeta₁_one, riemannZeta₁_one, div_one, one_mul, sub_self,
    zero_mul, add_zero]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
