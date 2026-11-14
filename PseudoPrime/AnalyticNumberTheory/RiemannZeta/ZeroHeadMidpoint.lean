/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroAntiderivative
import PseudoPrime.Analysis.MidpointError

/-! # Midpoint approximation for integrated critical-line terms -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For positive ordered endpoints and `ρ + 1 ≠ 0`, the real part of the
integrated critical-line term equals the real part of its antiderivative.
This identifies a low-zero contribution with an ordinary real integral. -/
theorem integral_re_cpow_div {ρ : ℂ} (hρ1 : ρ + 1 ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (((t : ℂ) ^ ρ) / ρ).re) =
      (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))).re := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ ρ / ρ) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact
      ((Complex.continuousAt_ofReal_cpow_const t ρ
              (Or.inr (ne_of_gt (lt_of_lt_of_le ha ht.1)))).div_const
          ρ).continuousWithinAt
  have he := Complex.reCLM.intervalIntegral_comp_comm hi
  simp only [Complex.reCLM_apply] at he
  rw [he, intervalIntegral.integral_div, integral_cpow_pos ha hab hρ1]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- On a positive interval, the midpoint approximation to the integrated
real part of `t^ρ / ρ` has cubic error at most
`‖ρ - 1‖ * a^(-3/2) * (b - a)^3 / 24` when `ρ` lies on the critical line.
The proof bounds its explicit second derivative by its norm at the left endpoint. -/
theorem cpow_div_midpoint_error {ρ : ℂ} (hρ : ρ ≠ 0) (hρ1 : ρ - 1 ≠ 0) (hr : ρ.re = 1 / 2) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    |(∫ t in a..b, (((t : ℂ) ^ ρ) / ρ).re) - (b - a) * ((((↑((a + b) / 2) : ℂ) ^ ρ) / ρ).re)| ≤
      ‖ρ - 1‖ * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24 := by
  apply
    Analysis.midpoint_integral_error hab (f' := fun t : ℝ ↦ (((t : ℂ) ^ (ρ - 1))).re) (f'' :=
      fun t : ℝ ↦ ((ρ - 1) * (t : ℂ) ^ (ρ - 1 - 1)).re)
  · intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h := (hasDerivAt_ofReal_cpow_const ht0 hρ).div_const ρ
    have he : (ρ * (t : ℂ) ^ (ρ - 1)) / ρ = (t : ℂ) ^ (ρ - 1) := by
      rw [mul_comm, mul_div_cancel_right₀ _ hρ]
    rw [he] at h
    have h' := (hasDerivAt_const t Complex.reCLM).clm_apply h
    simpa only [zero_apply, zero_add, Complex.reCLM_apply] using h'
  · intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h := hasDerivAt_ofReal_cpow_const ht0 hρ1
    have h' := (hasDerivAt_const t Complex.reCLM).clm_apply h
    simpa only [zero_apply, zero_add, Complex.reCLM_apply] using h'
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    calc
      _ ≤ ‖(ρ - 1) * (t : ℂ) ^ (ρ - 1 - 1)‖ := Complex.abs_re_le_norm _
      _ = ‖ρ - 1‖ * t ^ (-(3 / 2 : ℝ)) := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        congr 1
        simp only [Complex.sub_re, Complex.one_re, hr]
        norm_num only
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha ht.1 (by norm_num only))
          (norm_nonneg _)

/-- For a finite set of critical-line points with nonnegative weights, bound the
integrated sum's difference from its midpoint sum. Summing the individual
quadrature errors retains all cancellation in the midpoint sum. -/
theorem weighted_head_midpoint_error (S : Finset ℂ) (w : ℂ → ℝ) (hw : ∀ ρ ∈ S, 0 ≤ w ρ)
    (hr : ∀ ρ ∈ S, ρ.re = 1 / 2) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |(∑ ρ ∈ S, (w ρ : ℂ) * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))).re -
          (b - a) * (∑ ρ ∈ S, (w ρ : ℂ) * ((↑((a + b) / 2) : ℂ) ^ ρ / ρ)).re| ≤
      (∑ ρ ∈ S, w ρ * ‖ρ - 1‖) * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24 := by
  have h (ρ : ℂ) (hρ : ρ ∈ S) :
    |w ρ * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))).re -
          (b - a) * (w ρ * ((↑((a + b) / 2) : ℂ) ^ ρ / ρ).re)| ≤
      w ρ * ‖ρ - 1‖ * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24 := by
    have h0 : ρ ≠ 0 := by
      intro hz
      have hh := hr ρ hρ
      simp only [hz, Complex.zero_re] at hh
      norm_num only at hh
    have h1 : ρ - 1 ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re, hr ρ hρ] at hh
      norm_num only at hh
    have hp : ρ + 1 ≠ 0 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re, hr ρ hρ] at hh
      norm_num only at hh
    have ht := cpow_div_midpoint_error h0 h1 (hr ρ hρ) ha hab
    rw [integral_re_cpow_div hp ha hab] at ht
    have hm := mul_le_mul_of_nonneg_left ht (hw ρ hρ)
    rw [← abs_of_nonneg (hw ρ hρ), ← abs_mul, abs_of_nonneg (hw ρ hρ)] at hm
    convert hm using 1 <;> congr 1 <;> ring
  have hs :=
    Finset.abs_sum_le_sum_abs
      (fun ρ ↦
        w ρ * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))).re -
          (b - a) * (w ρ * ((↑((a + b) / 2) : ℂ) ^ ρ / ρ).re))
      S
  have ht := Finset.sum_le_sum h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  simp only [Complex.re_sum, Complex.re_ofReal_mul] at ⊢
  have he :
    (∑ ρ ∈ S, w ρ * ‖ρ - 1‖ * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24) =
      (∑ ρ ∈ S, w ρ * ‖ρ - 1‖) * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24 := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  linarith only [hs, ht, he]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
