/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2

/-! # Shifted reciprocal zero sum at height 40 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Bound the shifted reciprocal weight for ordinates at least six. Splitting
at ten and completing a square retains the small correction near height 20. -/
private theorem shifted_scalar_40 {g : ℝ} (hg : 6 ≤ g) :
    (g ^ 2 + 1 / 4) * (1 / g - 1 / 40) ≤ (640401 / 64000 : ℝ) := by
  have hg0 : 0 < g := by linarith only [hg]
  have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0.ne'
  have hid : (g ^ 2 + 1 / 4) * (1 / g - 1 / 40) = g - g ^ 2 / 40 + 1 / (4 * g) - 1 / 160 := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = g - g ^ 2 * 40⁻¹ + 4⁻¹ * g⁻¹ - 160⁻¹ + (g⁻¹ * g - 1) * g := by ring
      _ = _ := by
        rw [mul_comm g⁻¹ g, hg1]; ring
  rw [hid]
  by_cases h : g ≤ 10
  · have hp : 0 ≤ (10 - g) * (30 - g) := mul_nonneg (by linarith only [h]) (by linarith only [h])
    have hbound : g - g ^ 2 / 40 ≤ 15 / 2 := by nlinarith only [hp]
    have hinv : 1 / (4 * g) ≤ 1 / 24 := by
      apply (div_le_iff₀ (by nlinarith only [hg] : 0 < 4 * g)).2
      nlinarith only [hg]
    linarith only [hbound, hinv]
  · have hten : 10 ≤ g := le_of_not_ge h
    have hinv : 1 / (80 * g) ≤ 1 / 800 := by
      apply (div_le_iff₀ (by nlinarith only [hg] : 0 < 80 * g)).2
      nlinarith only [hten]
    have hv : -(g - 20) / (80 * g) ≤ |g - 20| / 800 := by
      calc
        -(g - 20) / (80 * g) ≤ |g - 20| * (1 / (80 * g)) := by
          rw [div_eq_mul_inv, one_div]
          exact
            mul_le_mul_of_nonneg_right (neg_le_abs (g - 20))
              (inv_nonneg.mpr (by nlinarith only [hg]))
        _ ≤ |g - 20| / 800 := by
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul_of_nonneg_left hinv (abs_nonneg (g - 20))
    have hs := sq_nonneg (|g - 20| - 1 / 40)
    have ha : |g - 20| ^ 2 = (g - 20) ^ 2 := sq_abs _
    have hv' : -((g - 20) / (80 * g)) ≤ |g - 20| / 800 := by simpa only [neg_div] using hv
    have hre :
      g - g ^ 2 / 40 + 1 / (4 * g) - 1 / 160 =
        10 + 1 / 160 - (g - 20) ^ 2 / 40 - (g - 20) / (80 * g) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        _ = (10 + 160⁻¹ - (g - 20) ^ 2 * 40⁻¹ - (g - 20) * (g⁻¹ * 80⁻¹)) + (g * g⁻¹ - 1) / 80 := by
          ring
        _ = _ := by
          rw [hg1]; ring
    rw [hre]
    nlinarith only [hv', hs, ha]

/-- Under RH, the reciprocal zero sum through height 40 minus one fortieth
of the multiplicity count is bounded by the total inverse-square zero mass.
The shifted weight is bounded uniformly for ordinates above `2π`. -/
theorem zeroReciprocal_shift40 (hRH : RiemannHypothesis) :
    zeroReciprocalSum 40 - zeroCount 40 / 40 ≤ (231 / 5000 : ℝ) * (640401 / 64000) := by
  let S := zerosUpTo 40
  have hz : ∀ ρ ∈ S, riemannZeta ρ = 0 := by
    intro ρ hρ
    exact ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 40)).1 hρ).1
  have hre : ∀ ρ ∈ S, 0 ≤ ρ.re := by
    intro ρ hρ
    exact ((mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 40)).1 hρ).2.1
  have hm := sum_zetaZeroMultiplicity_invNormSq_le hRH S hz hre
  have hm' : (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) ≤ 231 / 5000 := by
    have hh := RiemannXi.riemannZeroMass_le_231_div_10000
    linarith only [hm, hh]
  have ht :
    ∀ ρ ∈ S,
      (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / 40) ≤
        ((riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ) * (640401 / 64000) := by
    intro ρ hρ
    have hg := zero_height_gt_two_pi hRH (hz ρ hρ) (hre ρ hρ)
    have hg6 : 6 ≤ |ρ.im| := by linarith only [hg, Real.pi_gt_three]
    have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg (hz ρ hρ) (hre ρ hρ)
    have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
    have hn : 0 < Complex.normSq ρ := by
      have hh := zero_norm_ge20 hRH (hz ρ hρ) (hre ρ hρ)
      linarith only [hh]
    have hscalar := shifted_scalar_40 hg6
    have he : Complex.normSq ρ = |ρ.im| ^ 2 + 1 / 4 := by
      rw [Complex.normSq_apply, hr, sq_abs]
      ring
    rw [← he] at hscalar
    have hw : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ :=
      div_nonneg (Nat.cast_nonneg _) hn.le
    have hh := mul_le_mul_of_nonneg_left hscalar hw
    have heq :
      (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ *
          (Complex.normSq ρ * (1 / |ρ.im| - 1 / 40)) =
        (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / 40) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hn.ne']
    rw [heq] at hh
    exact hh
  have hsum := Finset.sum_le_sum ht
  rw [← Finset.sum_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_right hm' (by norm_num only : (0 : ℝ) ≤ 640401 / 64000)
  rw [zeroReciprocalSum_eq, zeroCount_eq_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) * (1 / |ρ.im| - 1 / 40) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      ring
    _ ≤ _ := hsum.trans hmul

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
