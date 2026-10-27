/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorRefinedBounds

/-! # Adaptive centered Poisson bounds for the Gamma resolvent

Later nodes use the sharper Gamma correction 9/10.
The exact finite weighted Euler allowance is below 211/10.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational Euler allowance at scale a plus its archimedean correction.
 Nodes a≥3/2 use 9/10; earlier nodes retain 8/5. Certified dyadic denominators are unchanged.
 This defines the improved per-node centered error. -/
noncomputable def gammaResolventAdaptiveEulerError (a : ℚ) : ℝ :=
  (((a : ℝ) - 1 / 2)⁻¹ ^ 2 + ((a : ℝ) + 1 / 2)⁻¹) /
      (1 + (gammaResolventDyadicLower a : ℝ) / ((a : ℝ) - 1 / 2)) +
    (if (3 / 2 : ℝ) ≤ (a : ℝ) then 9 / 10 else 8 / 5)

/-- The absolute weighted adaptive errors sum to less than 211/10.
 Evaluate the exact rational expressions in the kernel. This is the new additive mass budget. -/
theorem gammaResolvent_adaptive_error_lt :
    (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * gammaResolventAdaptiveEulerError ab.1)).sum <
      (211 / 10 : ℝ) := by
  norm_num only [gammaResolventCoefficients, gammaResolventAdaptiveEulerError,
    gammaResolventDyadicLower, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true,
    ite_false]

/-- Certified adaptive Poisson errors imply the signed resolvent bound with additive 211/10.
 Keep signs in the conductor coefficient and use absolute weights only for the errors.
 This connects the improved finite certificate to actual Poisson sums. -/
theorem gammaResolvent_weighted_lt_of_adaptive_bounds (P : ℚ → ℝ) (L : ℝ)
    (h :
      ∀ ab ∈ gammaResolventCoefficients, |P ab.1 - L / 2| ≤ gammaResolventAdaptiveEulerError ab.1) :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + 211 / 10 := by
  have ht :=
    sum_signed_centered_le gammaResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ gammaResolventAdaptiveEulerError ab.1) (L / 2) h
  have he :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ = ((gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right gammaResolvent_adaptive_error_lt _)

end PseudoPrime.Analysis

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
