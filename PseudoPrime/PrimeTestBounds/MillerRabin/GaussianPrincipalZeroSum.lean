/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalError
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Interchanging ζ zeros and the centered principal functional -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a nonnegative finite interval, the integrable weight times the square-root
zero mass justifies termwise integration of the logarithmic explicit formula. -/
private theorem principal_log_zero_integral {Q : ℝ → ℝ} (hRH : RiemannHypothesis) {X a b : ℝ}
    (hX : 0 < X) (ha : 0 ≤ a) (hab : a ≤ b) (hQ : IntervalIntegrable Q MeasureTheory.volume a b) :
    HasSum
      (fun ρ : ℂ ↦
        ∫ u in a..b, (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (X * u) ρ).re * Q u)
      (∫ u in a..b, gaussianLogZetaZeroSum (X * u) * Q u) := by
  let w := AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2
  let S := Function.support w
  have hw : Summable w :=
    AnalyticNumberTheory.RiemannXi.summable_inversePowerZeroWeight (by norm_num only)
  let _ : Countable S := hw.countable_support.to_subtype
  let f := fun (ρ : ℂ) (u : ℝ) ↦
    (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (X * u) ρ).re * Q u
  have hzero (ρ : ℂ) (hρ : ρ ∉ S) {u : ℝ} (hu : 0 ≤ u) : f ρ u = 0 := by
    have hz : w ρ = 0 := Function.notMem_support.mp hρ
    have hn := gaussian_log_term_norm hRH (mul_nonneg hX.le hu) ρ
    rw [show AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight 2 ρ = 0 from hz, mul_zero,
      norm_eq_zero] at hn
    simp only [f, hn, Complex.zero_re, zero_mul]
  have hI : Function.support (fun ρ ↦ ∫ u in a..b, f ρ u) ⊆ S := by
    intro ρ hρ
    by_contra he
    apply hρ
    rw [← intervalIntegral.integral_zero]
    exact intervalIntegral.integral_congr_Ioo_of_le hab (fun u hu ↦ hzero ρ he (ha.trans hu.1.le))
  apply (hasSum_subtype_iff_of_support_subset hI).mp
  let C := Real.sqrt (X * b)
  let B := fun (ρ : S) (u : ℝ) ↦ (C * w ρ.val) * |Q u|
  have hs := hw.subtype (fun ρ ↦ ρ ∈ S)
  refine
    intervalIntegral.hasSum_integral_of_dominated_convergence (F := fun ρ : S ↦ f ρ) B ?_ ?_ ?_ ?_
      ?_
  · intro ρ
    have hmul : Continuous (fun u : ℝ ↦ X * u) := continuous_const.mul continuous_id
    have hc := Complex.continuous_re.comp ((gaussian_log_term_continuous hRH ρ.val).comp hmul)
    exact hc.aestronglyMeasurable.mul hQ.aestronglyMeasurable_restrict_uIoc
  · intro ρ
    filter_upwards with u hu
    have hu' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
    rw [Real.norm_eq_abs, show f ρ u = _ from rfl, abs_mul]
    refine mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans ?_) (abs_nonneg _)
    rw [gaussian_log_term_norm hRH (mul_nonneg hX.le (ha.trans hu'.1.le))]
    exact
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hu'.2 hX.le))
        (AnalyticNumberTheory.RiemannXi.inversePowerZeroWeight_nonneg 2 ρ.val)
  · filter_upwards with u _
    exact (hs.mul_left C).mul_right |Q u|
  · have hfun : (fun u ↦ ∑' ρ : S, B ρ u) = (fun u ↦ (C * ∑' ρ : S, w ρ.val) * |Q u|) := by
      funext u
      simp only [B, tsum_mul_left, tsum_mul_right]
    rw [hfun]
    exact hQ.abs.const_mul _
  · filter_upwards with u hu
    have hu' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
    have hu₀ := ha.trans_lt hu'.1
    have h :=
      (Complex.reCLM.hasSum (gaussian_log_zero_summable hRH (mul_pos hX hu₀)).hasSum).mul_right
        (Q u)
    have hf : Function.support (fun ρ ↦ f ρ u) ⊆ S := by
      intro ρ hρ
      by_contra he
      exact hρ (hzero ρ he hu₀.le)
    exact (hasSum_subtype_iff_of_support_subset hf).mpr h

/-- For an integrable weight, the centered zero term is the convergent sum
of the individually centered logarithmic zero contributions under RH. -/
public theorem principal_zero_hasSum (Q : ℝ → ℝ) (edge : ℝ) (hRH : RiemannHypothesis) {X y : ℝ}
    (hX : 0 < X) (hy : 1 ≤ y) (h₁ : IntervalIntegrable Q MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable Q MeasureTheory.volume 1 y) :
    HasSum
      (fun ρ : ℂ ↦
        principalErrorFunctional Q
          (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) edge X y)
      (principalErrorFunctional Q gaussianLogZetaZeroSum edge X y) := by
  have hi := principal_log_zero_integral hRH hX le_rfl zero_le_one h₁
  have hj := principal_log_zero_integral hRH hX zero_le_one hy h₂
  have he := (Complex.reCLM.hasSum (gaussian_log_zero_summable hRH hX).hasSum).mul_left (4 * edge)
  exact ((hi.mul_left 3).sub hj).sub he

/-- For either high kernel, integrate the centered logarithmic zero series term by term. -/
public theorem high_principal_zero_hasSum (K : HighGaussianKernel) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    HasSum
      (fun ρ : ℂ ↦
        principalErrorFunctional (deriv F)
          (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) (F 1) X
          (Real.exp 5))
      (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5)) := by
  intro d W F
  have hb : (0 : ℝ) < 5 := by norm_num only
  have hi := reflected_principal_integrable K.realProfile (sub_pos.mpr (high_gaussian_pole_gt K)) hb
  exact principal_zero_hasSum (deriv F) (F 1) hRH hX (Real.one_le_exp hb.le) hi.1 hi.2

end PseudoPrime.PrimeTestBounds.MillerRabin
