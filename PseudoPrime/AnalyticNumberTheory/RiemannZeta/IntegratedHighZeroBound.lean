/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZeroExclusion

/-! # High-zero contributions to the integrated explicit formula

Bound each contribution by its inverse-square ordinate weight.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a nontrivial zeta zero contributes at most its multiplicity
times the sum of the endpoint `3/2` powers divided by its squared ordinate.
Use the triangle inequality and the imaginary parts of both denominator factors. -/
theorem high_term (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
          (ρ * (ρ + 1))‖ ≤
      (riemannZetaZeroMultiplicity ρ : ℝ) * (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / |ρ.im| ^ 2 := by
  have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
  have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have haNorm : ‖(a : ℂ) ^ (ρ + 1)‖ = a ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.add_re, Complex.one_re, hr]
    congr 1
    ring
  have hbNorm : ‖(b : ℂ) ^ (ρ + 1)‖ = b ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.add_re, Complex.one_re, hr]
    congr 1
    ring
  have hn1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hn2 : |ρ.im| ≤ ‖ρ + 1‖ := by
    have h := Complex.abs_im_le_norm (ρ + 1)
    simpa only [Complex.add_im, Complex.one_im, add_zero] using h
  have hn : |ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
    rw [norm_mul]
    nlinarith only [mul_le_mul hn1 hn2 (abs_nonneg ρ.im) (norm_nonneg ρ)]
  have hden : 0 < |ρ.im| ^ 2 := by
    have hgap := zero_height_gt_two_pi hRH hz hre
    have hp : 0 < 2 * Real.pi := by positivity
    exact sq_pos_of_pos (lt_trans hp hgap)
  have hnum :
    ‖(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1))‖ ≤
      (riemannZetaZeroMultiplicity ρ : ℝ) * (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) := by
    rw [norm_mul, Complex.norm_natCast]
    exact
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans_eq (by rw [haNorm, hbNorm]))
        (Nat.cast_nonneg _)
  have hnn : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) * (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg ha.le _))
  rw [norm_div]
  exact
    (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans (div_le_div_of_nonneg_left hnn hden hn)

/-- Under RH, bound a finite sum of integrated zero contributions divided
by a positive width by the endpoint factor times the inverse-square ordinate
sum. The normalization retains the full inverse width. -/
theorem high_sum (hRH : RiemannHypothesis) (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0)
    (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    ‖∑ ρ ∈ S,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))‖ /
        h ≤
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / h *
        ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 := by
  have ht :
    ∀ ρ ∈ S,
      ‖(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1))‖ ≤
        (riemannZetaZeroMultiplicity ρ : ℝ) * (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / |ρ.im| ^ 2 :=
    fun ρ hρ ↦ high_term hRH (hz ρ hρ) (hre ρ hρ) ha hb
  have hsum := (norm_sum_le S _).trans (Finset.sum_le_sum ht)
  have heq :
    (∑ ρ ∈ S,
        (riemannZetaZeroMultiplicity ρ : ℝ) * (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / |ρ.im| ^ 2) =
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) *
        ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  rw [heq] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum hh.le
  calc
    _ ≤
        ((b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) *
            ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) /
          h :=
      hdiv
    _ = _ := by ring

/-- Under RH, any upper bound `C` on a finite inverse-square ordinate sum
bounds the corresponding width-normalized zero contribution. The bound `C`
is an explicit hypothesis, suitable for a later high-zero tail estimate. -/
theorem high_sum_of_tail (hRH : RiemannHypothesis) (S : Finset ℂ) (hz : ∀ ρ ∈ S, riemannZeta ρ = 0)
    (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {a b h C : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hC : (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤ C) :
    ‖∑ ρ ∈ S,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))‖ /
        h ≤
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / h * C := by
  have hfactor : 0 ≤ (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / h :=
    div_nonneg (add_nonneg (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg ha.le _)) hh.le
  exact (high_sum hRH S hz hre ha hb hh).trans (mul_le_mul_of_nonneg_left hC hfactor)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
