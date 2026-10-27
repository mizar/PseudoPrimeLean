/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorPrefixBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaAdaptivePoissonBounds

/-! # Eight-term per-node Poisson error certificate

Real digamma prefixes replace uniform Gamma corrections.
The signed resolvent retains its conductor coefficient with additive error below 199/10.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The certified rational Euler ratio plus the eight-term digamma allowance at the
 lower real Gamma argument of a resolvent node. This retains the exact node dependence
 and supplies the centered Poisson error. -/
noncomputable def gammaResolventPrefixEulerError (a : ℚ) : ℝ :=
  (((a : ℝ) - 1 / 2)⁻¹ ^ 2 + ((a : ℝ) + 1 / 2)⁻¹) /
      (1 + (gammaResolventDyadicLower a : ℝ) / ((a : ℝ) - 1 / 2)) +
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance ((1 / 2 + (a : ℝ)) / 2) 8

/-- The absolute weighted node-dependent errors sum to less than 199/10.
 Evaluate the signed coefficient list, dyadic denominators and eight-term rational prefixes.
 This is the improved additive zero-mass certificate. -/
theorem gammaResolvent_prefix_error_lt :
    (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * gammaResolventPrefixEulerError ab.1)).sum <
      (199 / 10 : ℝ) := by
  norm_num only [gammaResolventCoefficients, gammaResolventPrefixEulerError,
    gammaResolventDyadicLower, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance, Finset.sum_range_succ, Finset.sum_range_zero,
    max_def, ite_true, ite_false]

/-- Given the certified prefix errors for actual Poisson values, their signed resolvent
 combination is below M L+199/10. Preserve the signed conductor term and bound only the errors
 by absolute weights. This connects the finite certificate with the analytic sums. -/
theorem gammaResolvent_weighted_lt_of_prefix_bounds (P : ℚ → ℝ) (L : ℝ)
    (h :
      ∀ ab ∈ gammaResolventCoefficients, |P ab.1 - L / 2| ≤ gammaResolventPrefixEulerError ab.1) :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + 199 / 10 := by
  have ht :=
    sum_signed_centered_le gammaResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ gammaResolventPrefixEulerError ab.1) (L / 2) h
  have he :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ = ((gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right gammaResolvent_prefix_error_lt _)

end PseudoPrime.Analysis

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under primitive nonprincipal individual RH with nonprincipal inverse, sigma in
 [1,15/2] and a certified lower Gamma argument R, the centered Poisson sum is at most
 the ordinary derivative norm plus the m-term Gamma prefix allowance.
 Use the exact completed identity and both Gamma-factor parity shifts. -/
theorem completed_poissonSum_centered_le_ordinary_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 15 / 2) {R : ℝ} (hR : 1 / 2 ≤ R)
    (hRσ : R ≤ σ / 2) (m : ℕ) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))) -
          Real.log q / 2| ≤
      ‖logDeriv χ.LFunction (σ : ℂ)‖ + Gamma.gammaPrefixAllowance R m := by
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
        (abs_re_logDeriv_gammaFactor_le_prefix χ hσ hσu hR hRσ m))

/-- For every certified resolvent node under primitive nonprincipal individual RH,
 the centered Poisson sum is bounded by its eight-term prefix Euler error.
 Combine the actual ordinary Euler ratio with dyadic certification and real Gamma prefixes.
 This supplies the unconditional analytic per-node inputs for the new mass bound. -/
theorem completed_poissonSum_centered_le_resolvent_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ))) -
          Real.log q / 2| ≤
      Analysis.gammaResolventPrefixEulerError ab.1 := by
  have hal := List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab
  have hau := (List.forall_iff_forall_mem.mp Analysis.gammaResolvent_gamma_arguments ab hab).2.2
  have halR := (Rat.cast_lt (K := ℝ)).mpr hal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at halR
  have hauR := (Rat.cast_le (K := ℝ)).mpr hau
  norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at hauR
  have hr : 0 < (ab.1 : ℝ) - 1 / 2 := sub_pos.mpr halR
  have hs : 1 ≤ 1 / 2 + (ab.1 : ℝ) := by linarith only [halR]
  have hsu : 1 / 2 + (ab.1 : ℝ) ≤ 15 / 2 := by linarith only [hauR]
  have hb :=
    completed_poissonSum_centered_le_ordinary_prefix hq hRH hp hne hinv hs hsu
      (show 1 / 2 ≤ (1 / 2 + (ab.1 : ℝ)) / 2 by linarith only [hs]) (le_refl _) 8
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
  simpa only [Analysis.gammaResolventPrefixEulerError, Complex.ofReal_add] using
    hb.trans
      (add_le_add_left (hL.trans hcmp) (Gamma.gammaPrefixAllowance ((1 / 2 + (ab.1 : ℝ)) / 2) 8))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
