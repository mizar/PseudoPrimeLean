/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogOriginRegularization
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Unconditional normalized zero-sum limits for a fixed character -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a nonprincipal character and a positive real scale, the norm of each
logarithmic completed-zero term divided by the scale is its inverse-square
multiplicity mass times `x^(Re ρ-1)`. Analyticity makes multiplicities nonnegative.
This exposes pointwise decay without RH. -/
theorem norm_completedLogZeroTerm_div_scale_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖completedLogZeroTerm χ x ρ / (x : ℂ)‖ =
      x ^ (ρ.re - 1) *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ) := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hD : 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hxnorm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.le]
  rw [Real.rpow_sub hx, Real.rpow_one]
  simp only [completedLogZeroTerm, norm_div, norm_mul, norm_pow, Complex.norm_intCast,
    abs_of_nonneg hD, Complex.norm_cpow_eq_rpow_re_of_pos hx, hxnorm, Complex.normSq_eq_norm_sq]
  ring

/-- For every fixed nonprincipal character and zero parameter, the normalized
logarithmic zero term tends to zero. Terms of zero divisor vanish identically;
otherwise the unconditional zero-free right half-plane gives `Re ρ < 1`.
This is the pointwise input to dominated convergence. -/
theorem tendsto_completedLogZeroTerm_div_scale {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (ρ : ℂ) :
    Filter.Tendsto (fun x : ℝ ↦ completedLogZeroTerm χ x ρ / (x : ℂ)) Filter.atTop (nhds 0) := by
  by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
  · simpa only [completedLogZeroTerm, hD, Int.cast_zero, zero_mul, zero_div] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ ↦ (0 : ℂ)) Filter.atTop (nhds 0))
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hre := completedLFunction_zero_re_lt_one hne hz
    have hr : Filter.Tendsto (fun x : ℝ ↦ x ^ (ρ.re - 1)) Filter.atTop (nhds 0) := by
      have h := tendsto_rpow_neg_atTop (sub_pos.mpr hre)
      simpa only [neg_sub] using h
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hm :=
      hr.mul_const ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ)
    have heq :
      (fun x : ℝ ↦ ‖completedLogZeroTerm χ x ρ / (x : ℂ)‖) =ᶠ[Filter.atTop]
        (fun x ↦
          x ^ (ρ.re - 1) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ)) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      exact norm_completedLogZeroTerm_div_scale_eq hne hx ρ
    simpa only [zero_mul] using hm.congr' heq.symm

/-- For a nonprincipal character and scale at least one, every normalized
logarithmic zero term is bounded by its inverse-square divisor mass. Divide the
unconditional full-scale majorant by the positive scale. The majorant is independent
of the scale and is summable for primitive characters. -/
theorem norm_completedLogZeroTerm_div_scale_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (ρ : ℂ) :
    ‖completedLogZeroTerm χ x ρ / (x : ℂ)‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le]
  apply (div_le_iff₀ hxpos).mpr
  exact (norm_completedLogZeroTerm_le_unconditionally hne hx ρ).trans_eq (mul_comm _ _)

/-- For a fixed primitive nonprincipal character with nonprincipal inverse and
modulus at least two, the full logarithmic zero sum divided by the scale tends
to zero. Apply dominated convergence to the unconditional inverse-square mass.
This requires no quantitative zero-free region and no RH. -/
theorem tendsto_tsum_completedLogZeroTerm_div_scale_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto (fun x : ℝ ↦ (∑' ρ : ℂ, completedLogZeroTerm χ x ρ) / (x : ℂ)) Filter.atTop
      (nhds 0) := by
  have ht :=
    tendsto_tsum_of_dominated_convergence
      (summable_divisor_div_normSq_unconditionally hq hp hne hinv)
      (fun ρ ↦ tendsto_completedLogZeroTerm_div_scale hne ρ)
      (by
        filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
        exact fun ρ ↦ norm_completedLogZeroTerm_div_scale_le hne hx ρ)
  simpa only [tsum_zero, tsum_div_const] using ht

/-- For a fixed primitive nonprincipal character and its nonprincipal inverse,
the half-scale zero sum divided by the scale tends to zero. Subtract the normalized
full sums at `x` and `x/2`, retaining the factor one half. This transfers the
fixed-character decay to the half-scale formula. -/
theorem tendsto_tsum_completedLogHalfZeroTerm_div_scale_unconditionally {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto (fun x : ℝ ↦ (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) / (x : ℂ)) Filter.atTop
      (nhds 0) := by
  have hfull := tendsto_tsum_completedLogZeroTerm_div_scale_unconditionally hq hp hne hinv
  have htop : Filter.Tendsto (fun x : ℝ ↦ x / 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num only : (0 : ℝ) < 2) Filter.tendsto_id
  have hhalf := (hfull.comp htop).const_mul (1 / 2 : ℂ)
  have hlim := hfull.sub hhalf
  have heq :
    (fun x : ℝ ↦ (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) / (x : ℂ)) =ᶠ[Filter.atTop]
      (fun x ↦
        (∑' ρ : ℂ, completedLogZeroTerm χ x ρ) / (x : ℂ) -
          (1 / 2 : ℂ) * ((∑' ρ : ℂ, completedLogZeroTerm χ (x / 2) ρ) / ((x / 2 : ℝ) : ℂ))) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    rw [tsum_completedLogHalfZeroTerm_eq_sub_unconditionally hq hp hne hinv hx, sub_div,
      Complex.ofReal_div, Complex.ofReal_ofNat, div_div_eq_mul_div]
    ring
  simpa only [mul_zero, sub_zero] using hlim.congr' heq.symm

/-- Every fixed complex constant divided by a real scale tends to zero as the
scale tends to positive infinity. Transport the real inverse limit to the complex
numbers and multiply by the constant. This removes fixed genus corrections. -/
theorem tendsto_complex_const_div_scale (a : ℂ) :
    Filter.Tendsto (fun x : ℝ ↦ a / (x : ℂ)) Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun x : ℝ ↦ (x : ℂ)⁻¹) Filter.atTop (nhds 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp tendsto_inv_atTop_zero
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using h
  simpa only [mul_zero, div_eq_mul_inv] using hi.const_mul a

/-- For a fixed primitive nonprincipal character with nonprincipal inverse, the
regularized logarithmic zero sum divided by the scale tends to zero. Subtract the
fixed genus correction from the half-scale zero sum. This connects dominated
convergence to the origin-free arithmetic formula. -/
theorem tendsto_tsum_regularizedLogHalfZeroTerm_div_scale_unconditionally {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto (fun x : ℝ ↦ (∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) / (x : ℂ)) Filter.atTop
      (nhds 0) := by
  have hhalf := tendsto_tsum_completedLogHalfZeroTerm_div_scale_unconditionally hq hp hne hinv
  have hconst :=
    tendsto_complex_const_div_scale
      ((Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0))
  have hlim := hhalf.sub hconst
  have heq :
    (fun x : ℝ ↦ (∑' ρ : ℂ, regularizedLogHalfZeroTerm χ x ρ) / (x : ℂ)) =ᶠ[Filter.atTop]
      (fun x ↦
        (∑' ρ : ℂ, completedLogHalfZeroTerm χ x ρ) / (x : ℂ) -
          ((Real.log 2 : ℂ) * (logDeriv χ.completedLFunction 2 - logDeriv χ.completedLFunction 0)) /
            (x : ℂ)) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx
    rw [tsum_regularizedLogHalfZeroTerm_eq_unconditionally hq hp hne hinv hx, sub_div]
  simpa only [sub_zero] using hlim.congr' heq.symm

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
