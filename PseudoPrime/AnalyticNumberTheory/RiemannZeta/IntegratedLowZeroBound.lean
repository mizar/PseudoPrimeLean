/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroAntiderivative

/-! # Low-zero contributions to the integrated explicit formula

Bound normalized finite zero sums by the inverse-height sum.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the width-normalized contribution of a nontrivial zeta zero
on `0 < a < b` is at most its multiplicity times `sqrt b / |Im ρ|`. Rewrite
the power difference as an integral and bound the integrand on the interval. -/
theorem low_term (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ‖(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1))‖ /
        (b - a) ≤
      (riemannZetaZeroMultiplicity ρ : ℝ) * Real.sqrt b / |ρ.im| := by
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have hρ1 : ρ + 1 ≠ 0 := by
    intro h
    have hr' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr'
    linarith only [hr, hr']
  have hg : 0 < |ρ.im| := by
    have h := zero_height_gt_two_pi hRH hz hre
    have hp : 0 < 2 * Real.pi := by positivity
    exact lt_trans hp h
  have hn : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hwidth : 0 < b - a := sub_pos.mpr hab
  have hI : ‖∫ t in a..b, (t : ℂ) ^ ρ‖ ≤ Real.sqrt b * (b - a) := by
    have hh :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := Real.sqrt b) (f :=
        fun t : ℝ ↦ (t : ℂ) ^ ρ)
        (by
          intro t ht
          have ht' : t ∈ Set.Icc a b := by
            rw [Set.uIoc_of_le hab.le] at ht
            exact ⟨ht.1.le, ht.2⟩
          have ht0 := lt_of_lt_of_le ha ht'.1
          rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0, hr, ← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_sqrt ht'.2)
    rw [abs_of_nonneg hwidth.le] at hh
    exact hh
  have heq :
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)) =
      (riemannZetaZeroMultiplicity ρ : ℂ) * (∫ t in a..b, (t : ℂ) ^ ρ) / ρ := by
    rw [integral_cpow_pos ha hab.le hρ1]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_natCast]
  have hm : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
  have hi :
    (riemannZetaZeroMultiplicity ρ : ℝ) * ‖∫ t in a..b, (t : ℂ) ^ ρ‖ ≤
      (riemannZetaZeroMultiplicity ρ : ℝ) * (Real.sqrt b * (b - a)) :=
    mul_le_mul_of_nonneg_left hI hm
  have hn0 : 0 < ‖ρ‖ := lt_of_lt_of_le hg hn
  have hdiv := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hi hn0.le) hwidth.le
  have hfrac :
    ((riemannZetaZeroMultiplicity ρ : ℝ) * (Real.sqrt b * (b - a)) / ‖ρ‖) / (b - a) =
      (riemannZetaZeroMultiplicity ρ : ℝ) * Real.sqrt b / ‖ρ‖ := by
    have hc := mul_inv_cancel₀ hwidth.ne'
    simp only [div_eq_mul_inv]
    linear_combination ((riemannZetaZeroMultiplicity ρ : ℝ) * Real.sqrt b * ‖ρ‖⁻¹) * hc
  have hc : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) * Real.sqrt b :=
    mul_nonneg hm (Real.sqrt_nonneg b)
  exact (hdiv.trans_eq hfrac).trans (div_le_div_of_nonneg_left hc hg hn)

/-- Under RH, bound a finite sum of normalized zero contributions by
`sqrt b` times the inverse-height sum. Apply the individual zero estimate
and the triangle inequality. -/
theorem low_sum (hRH : RiemannHypothesis) (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0)
    (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ‖∑ ρ ∈ S,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))‖ /
        (b - a) ≤
      Real.sqrt b * ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| := by
  have ht :
    ∀ ρ ∈ S,
      ‖(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))‖ /
          (b - a) ≤
        (riemannZetaZeroMultiplicity ρ : ℝ) * Real.sqrt b / |ρ.im| :=
    fun ρ hρ ↦ low_term hRH (hz ρ hρ) (hre ρ hρ) ha hab
  have hsum :=
    div_le_div_of_nonneg_right
      (norm_sum_le S
        (fun ρ ↦
          (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1))))
      (sub_nonneg.mpr hab.le)
  rw [Finset.sum_div] at hsum
  have hbound := hsum.trans (Finset.sum_le_sum ht)
  have heq :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) * Real.sqrt b / |ρ.im|) =
      Real.sqrt b * ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  exact hbound.trans_eq heq

/-- Under RH, the normalized contribution of all nontrivial zeros through
height `T ≥ 0` is bounded by `sqrt b` times the corresponding reciprocal
height sum. Apply the finite estimate to the closed-height zero ledger. -/
theorem low_sum_up_to (hRH : RiemannHypothesis) {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 < a)
    (hab : a < b) :
    ‖∑ ρ ∈ zerosUpTo T,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))‖ /
        (b - a) ≤
      Real.sqrt b * zeroReciprocalSum T := by
  rw [zeroReciprocalSum_eq]
  apply low_sum hRH (zerosUpTo T) _ _ ha hab
  · intro ρ hρ
    exact ((mem_zerosUpTo hT).1 hρ).1
  · intro ρ hρ
    exact ((mem_zerosUpTo hT).1 hρ).2.1

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
