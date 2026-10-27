/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogDerivativeNumericalBounds
public import PseudoPrime.Analysis.GammaResolventEulerCertificate

/-! # Centered Poisson bounds with explicit archimedean error

The conductor term is retained exactly. The centered error is bounded by the ordinary
logarithmic derivative and the fixed gamma-factor correction six.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character with individual RH and nonprincipal inverse,
the real Poisson sum at sigma in [1,15/2], centered by log q/2, has absolute value at most
the ordinary logarithmic-derivative norm plus six. Use the exact completed Poisson identity
and the ordinary/completed gamma-factor decomposition. This isolates the two error terms
in the signed resolvent certificate. -/
theorem completed_poissonSum_centered_le_ordinary {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 15 / 2) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
          Real.log q / 2| ≤
      ‖logDeriv χ.LFunction (σ : ℂ)‖ + 6 := by
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
      (add_le_add (Complex.abs_re_le_norm _) (abs_re_logDeriv_gammaFactor_le_six χ hσ hσu))

/-- For a primitive nonprincipal character satisfying individual RH and with nonprincipal
inverse, the real Poisson sum at 1 < sigma <= 15/2, centered by log q/2, has error at most
(sigma-1)^(-2)+(sigma-1)^(-1)+6. Combine the unconditional ordinary derivative bound
with the explicit archimedean correction. This supplies every resolvent node's centered error
without any additional analytic-bound hypothesis. -/
theorem completed_poissonSum_centered_le_inv_gap {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 < σ) (hσu : σ ≤ 15 / 2) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
          Real.log q / 2| ≤
      (σ - 1)⁻¹ ^ 2 + (σ - 1)⁻¹ + 6 := by
  exact
    (completed_poissonSum_centered_le_ordinary hq hRH hp hne hinv hσ.le hσu).trans
      (add_le_add_left (norm_logDeriv_real_le_inv_gap χ hσ) 6)

/-- For a primitive nonprincipal character with individual RH and nonprincipal inverse,
the real Poisson sum at sigma in [1,15/2], centered by log q/2, has absolute value at most
the ordinary logarithmic-derivative norm plus 8/5. Use the exact completed Poisson identity
and the ordinary/completed gamma-factor decomposition. This isolates the two error terms
in the signed resolvent certificate. -/
theorem completed_poissonSum_centered_le_ordinary_eight_fifths {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 15 / 2) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
          Real.log q / 2| ≤
      ‖logDeriv χ.LFunction (σ : ℂ)‖ + 8 / 5 := by
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
      (add_le_add (Complex.abs_re_le_norm _) (abs_re_logDeriv_gammaFactor_le_eight_fifths χ hσ hσu))

/-- For every certified resolvent node and a primitive nonprincipal character under
individual RH with nonprincipal inverse, the centered Poisson error is bounded by
the rational Euler allowance. Combine the ordinary Euler ratio and Gamma bound 8/5,
then replace the dyadic power by its certified rational lower bound. This supplies
the signed zero-mass certificate's individual analytic inputs. -/
theorem completed_poissonSum_centered_le_resolvent_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ))) -
          Real.log q / 2| ≤
      Analysis.gammaResolventEulerError ab.1 := by
  have hal := List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab
  have hau := (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_gamma_arguments ab hab).2.2
  have halR := (Rat.cast_lt (K := ℝ)).mpr hal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at halR
  have hauR := (Rat.cast_le (K := ℝ)).mpr hau
  norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at hauR
  have hr : 0 < (ab.1 : ℝ) - 1 / 2 := sub_pos.mpr halR
  have hs : 1 ≤ 1 / 2 + (ab.1 : ℝ) := by linarith only [halR]
  have hsu : 1 / 2 + (ab.1 : ℝ) ≤ 15 / 2 := by linarith only [hauR]
  have hb := completed_poissonSum_centered_le_ordinary_eight_fifths hq hRH hp hne hinv hs hsu
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
  simpa only [Analysis.gammaResolventEulerError, Complex.ofReal_add] using
    hb.trans (add_le_add_left (hL.trans hcmp) (8 / 5))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
