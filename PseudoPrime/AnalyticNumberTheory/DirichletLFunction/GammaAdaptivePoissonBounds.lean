/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorRefinedBounds
public import PseudoPrime.Analysis.GammaAdaptivePoissonBounds

/-! # Adaptive centered Poisson bounds for the Gamma resolvent

Later nodes use the sharper Gamma correction 9/10.
The exact finite weighted Euler allowance is below 211/10.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal individual RH data and sigma in [1,15/2], the centered
 Poisson sum is bounded by the ordinary derivative norm plus the adaptive Gamma correction.
 Use the exact completed Poisson identity and both Gamma-factor intervals.
 This preserves the conductor term while reducing errors at later nodes. -/
theorem completed_poissonSum_centered_le_ordinary_adaptive {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 15 / 2) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
          Real.log q / 2| ≤
      ‖logDeriv χ.LFunction (σ : ℂ)‖ + (if (2 : ℝ) ≤ σ then 9 / 10 else 8 / 5) := by
  have hr : 0 < (σ : ℂ).re := zero_lt_one.trans_le hσ
  have hs : 1 / 2 < (σ : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith only [hσ]
  have he := completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv hs
  simp only [Complex.ofReal_re] at he
  have hd :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hσ) (gammaFactor_ne_zero_of_re_pos χ hr)
      (analyticAt_gammaFactor_of_re_pos χ hr).differentiableAt
  have hf :
    logDeriv χ.completedLFunction (σ : ℂ) =
      logDeriv χ.LFunction (σ : ℂ) + logDeriv χ.gammaFactor (σ : ℂ) := by
    rw [hd]
    ring
  rw [he, add_sub_cancel_right, hf, Complex.add_re]
  exact
    (abs_add_le _ _).trans
      (add_le_add (Complex.abs_re_le_norm _)
        (by
          by_cases hs2 : (2 : ℝ) ≤ σ
          · rw [ite_eq_left hs2]
            exact abs_re_logDeriv_gammaFactor_le_nine_tenths χ hs2 hσu
          · rw [ite_eq_right hs2]
            exact abs_re_logDeriv_gammaFactor_le_eight_fifths χ hσ hσu))

/-- For each certified resolvent node, the centered Poisson sum is at most its adaptive
 Euler error under primitive nonprincipal individual RH. Combine the ordinary Euler ratio,
 dyadic denominator certificate and adaptive Gamma-factor bound.
 This supplies the analytic inputs for the improved finite mass certificate. -/
theorem completed_poissonSum_centered_le_resolvent_adaptive {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ))) -
          Real.log q / 2| ≤
      Analysis.gammaResolventAdaptiveEulerError ab.1 := by
  have hal := List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab
  have hau := (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_gamma_arguments ab hab).2.2
  have halR := (Rat.cast_lt (K := ℝ)).mpr hal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at halR
  have hauR := (Rat.cast_le (K := ℝ)).mpr hau
  norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at hauR
  have hr : 0 < (ab.1 : ℝ) - 1 / 2 := sub_pos.mpr halR
  have hs : 1 ≤ 1 / 2 + (ab.1 : ℝ) := by linarith only [halR]
  have hsu : 1 / 2 + (ab.1 : ℝ) ≤ 15 / 2 := by linarith only [hauR]
  have hb := completed_poissonSum_centered_le_ordinary_adaptive hq hRH hp hne hinv hs hsu
  have hn : 1 / 2 + (ab.1 : ℝ) - 1 / 2 = (ab.1 : ℝ) := by ring
  rw [hn] at hb
  have hL := norm_logDeriv_real_le_euler_ratio χ hr
  have he : 1 + ((ab.1 : ℝ) - 1 / 2) = 1 / 2 + (ab.1 : ℝ) := by ring
  rw [he] at hL
  have hd := Analysis.gammaResolvent_dyadic_lower_valid ab hab
  have hd0 := (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_dyadic_checks ab hab).1
  have hdR := (Rat.cast_le (K := ℝ)).mpr hd0
  norm_num only [Rat.cast_zero] at hdR
  have hden : 0 < 1 + (Analysis.gammaResolventDyadicLower ab.1 : ℝ) / ((ab.1 : ℝ) - 1 / 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hdR hr.le)
  have hcmp :=
    div_le_div_of_nonneg_left
      (add_nonneg (sq_nonneg ((ab.1 : ℝ) - 1 / 2)⁻¹)
        (inv_nonneg.mpr (by linarith only [hr] : 0 ≤ (ab.1 : ℝ) - 1 / 2 + 1)))
      hden (add_le_add_right (div_le_div_of_nonneg_right hd hr.le) 1)
  have hpoint : (ab.1 : ℝ) - 1 / 2 + 1 = (ab.1 : ℝ) + 1 / 2 := by ring
  rw [hpoint] at hL hcmp
  have htest : (2 : ℝ) ≤ 1 / 2 + (ab.1 : ℝ) ↔ (3 / 2 : ℝ) ≤ (ab.1 : ℝ) := by
    constructor <;> intro h <;> linarith only [h]
  simp only [htest] at hb
  simpa only [Analysis.gammaResolventAdaptiveEulerError, Complex.ofReal_add] using
    hb.trans (add_le_add_left (hL.trans hcmp) (if (3 / 2 : ℝ) ≤ (ab.1 : ℝ) then 9 / 10 else 8 / 5))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
