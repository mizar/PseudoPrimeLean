/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZeroExclusion
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Shifted reciprocal zero weights

Use the inverse-square zero mass and the low-zero gap to bound finite sums.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `0 < L ≤ g` and `0 < H`, bound the shifted reciprocal weight after
multiplication by `g² + 1/4`. Complete the square and compare reciprocals. -/
theorem scalar_bound {g L H : ℝ} (hL : 0 < L) (hLg : L ≤ g) (hH : 0 < H) :
    (g ^ 2 + 1 / 4) * (1 / g - 1 / H) ≤ H / 4 + 1 / (4 * L) := by
  have hg : 0 < g := lt_of_lt_of_le hL hLg
  have hs : g - g ^ 2 / H ≤ H / 4 := by
    have hsq := sq_nonneg (g - H / 2)
    have hdiv : (g * H - g ^ 2) / H ≤ H / 4 := (div_le_iff₀ hH).2 (by nlinarith only [hsq])
    have hid : (g * H - g ^ 2) / H = g - g ^ 2 / H := by
      rw [sub_div, mul_div_cancel_right₀ g hH.ne']
    linarith only [hdiv, hid]
  have hi : 1 / (4 * g) ≤ 1 / (4 * L) := by
    exact one_div_le_one_div_of_le (by nlinarith only [hL]) (by nlinarith only [hLg])
  have hn : 0 ≤ 1 / (4 * H) := div_nonneg (by norm_num only) (by nlinarith only [hH])
  have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg.ne'
  have hH1 : H * H⁻¹ = 1 := mul_inv_cancel₀ hH.ne'
  have hid : (g ^ 2 + 1 / 4) * (1 / g - 1 / H) = (g - g ^ 2 / H) + 1 / (4 * g) - 1 / (4 * H) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = (g - g ^ 2 * H⁻¹) + 4⁻¹ * g⁻¹ - 4⁻¹ * H⁻¹ + (g⁻¹ * g - 1) * g := by ring
      _ = _ := by
        rw [mul_comm g⁻¹ g, hg1]; ring
  linarith only [hid, hs, hi, hn]

/-- Under RH, every finite set of nontrivial zeta zeros satisfies the shifted
reciprocal sum bound for positive `H`. The low-zero gap bounds each summand
by a multiple of its inverse-square mass; summing uses the total mass bound. -/
theorem shifted_reciprocal_sum_le (hRH : RiemannHypothesis) (S : Finset ℂ) {H : ℝ} (hH : 0 < H)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / H)) ≤
      (H / 4 + 1 / (8 * Real.pi)) / 20 := by
  have hc : 0 ≤ H / 4 + 1 / (8 * Real.pi) := by positivity
  have hm := sum_zetaZeroMultiplicity_invNormSq_le hRH S hz hre
  have hm' : (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤ 1 / 20 := by
    have hh := RiemannXi.riemannZeroMass_le_one_fortieth
    linarith only [hm, hh]
  have ht :
    ∀ ρ ∈ S,
      (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / H) ≤
        ((riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) * (H / 4 + 1 / (8 * Real.pi)) := by
    intro ρ hρ
    have hg := zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
    have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
    have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
    have hn : 0 < Complex.normSq ρ := by
      have hh := zero_norm_ge20 hRH (hz ρ hρ) (hre ρ hρ)
      linarith only [hh]
    have hs := scalar_bound (show (0 : ℝ) < 2 * Real.pi by positivity) hg.le hH
    have he : Complex.normSq ρ = |ρ.im| ^ 2 + 1 / 4 := by
      rw [Complex.normSq_apply, hr, sq_abs]
      ring
    rw [← he] at hs
    have hw : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ :=
      div_nonneg (Nat.cast_nonneg _) hn.le
    have hh := mul_le_mul_of_nonneg_left hs hw
    have heq :
      (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ *
          (Complex.normSq ρ * (1 / |ρ.im| - 1 / H)) =
        (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / H) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hn.ne']
    have hc_eq : (H / 4 + 1 / (4 * (2 * Real.pi))) = H / 4 + 1 / (8 * Real.pi) := by
      congr 2
      ring
    rw [heq, hc_eq] at hh
    exact hh
  calc
    _ ≤
        ∑ ρ ∈ S,
          ((riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) * (H / 4 + 1 / (8 * Real.pi)) :=
      Finset.sum_le_sum ht
    _ =
        (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) *
          (H / 4 + 1 / (8 * Real.pi)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (1 / 20 : ℝ) * (H / 4 + 1 / (8 * Real.pi)) := mul_le_mul_of_nonneg_right hm' hc
    _ = _ := by ring

/-- Under RH, the difference between the finite inverse-height sum and the
multiplicity count divided by `H > 0` is at most `H / 80 + 1 / (160π)`.
Expand the shifted sum and apply its inverse-square mass bound. -/
theorem reciprocal_sum_sub_count (hRH : RiemannHypothesis) (S : Finset ℂ) {H : ℝ} (hH : 0 < H)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) -
        (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ)) / H ≤
      H / 80 + 1 / (160 * Real.pi) := by
  have h := shifted_reciprocal_sum_le hRH S hH hz hre
  have he :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / H)) =
      (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) -
        (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ)) / H := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  rw [he] at h
  convert h using 1
  ring

/-- Under RH, specialize the shifted inverse-height estimate at `2πe`.
Rational bounds for `π` and `e` give the upper bound `109 / 480`. -/
theorem reciprocal_sum_at_two_pi_e (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) -
        (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ)) / (2 * Real.pi * Real.exp 1) ≤
      (109 / 480 : ℝ) := by
  have hp : (0 : ℝ) < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have h := reciprocal_sum_sub_count hRH S hp hz hre
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    have hh := Real.pi_lt_d4
    norm_num only at hh ⊢
    linarith only [hh]
  have he : Real.exp 1 < (11 / 4 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
  have hprod := mul_le_mul hpi.le he.le (Real.exp_pos 1).le (show (0 : ℝ) ≤ 22 / 7 by norm_num only)
  have hH : 2 * Real.pi * Real.exp 1 ≤ 18 := by nlinarith only [hprod]
  have hlow : (0 : ℝ) < 160 * Real.pi := by nlinarith only [Real.pi_pos]
  have hinv : 1 / (160 * Real.pi) ≤ (1 / 480 : ℝ) := by
    apply (div_le_iff₀ hlow).2
    nlinarith only [Real.pi_gt_three]
  linarith only [h, hH, hinv]

/-- Under RH, the finite shifted inverse-height contribution at `2πe`,
plus the remaining rational budget `39 / 64`, is strictly less than one.
This is the initial constant needed in the reciprocal zero-sum estimate. -/
theorem reciprocal_initial_lt_one (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) -
          (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ)) / (2 * Real.pi * Real.exp 1) +
        39 / 64 <
      1 := by
  have h := reciprocal_sum_at_two_pi_e hRH S hz hre
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
