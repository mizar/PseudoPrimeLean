/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrefixZeroMass
public import PseudoPrime.Analysis.GammaVariablePrefixZeroMass

/-! # Variable-length digamma prefix error certificates

Any certified prefix error sum transfers to the actual Gamma zero mass.
A sixteen-term kernel-checked certificate gives additive 99/5.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under primitive nonprincipal individual RH, each certified resolvent node obeys its
 m-term centered error allowance. Combine the real Gamma prefix bound with the Euler ratio
 and dyadic denominator certificate. The proof applies to any natural prefix length. -/
theorem completed_poissonSum_centered_le_resolvent_with_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients)
    (m : ℕ) :
    |(∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ab.1 : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ) - ρ))) -
          Real.log q / 2| ≤
      Analysis.gammaResolventEulerErrorWithPrefix m ab.1 := by
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
      (show 1 / 2 ≤ (1 / 2 + (ab.1 : ℝ)) / 2 by linarith only [hs]) (le_refl _) m
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
  simpa only [Analysis.gammaResolventEulerErrorWithPrefix, Complex.ofReal_add] using
    hb.trans
      (add_le_add_left (hL.trans hcmp) (Gamma.gammaPrefixAllowance ((1 / 2 + (ab.1 : ℝ)) / 2) m))

/-- Under primitive nonprincipal individual RH, an m-term finite error certificate below C
 bounds the actual signed resolvent zero mass by Mlog(q)+C.
 Use its exact Poisson identity and the variable node comparison.
 This removes the fixed eight-term requirement from the mass interface. -/
theorem gammaResolvent_zeroMass_lt_of_prefix_error {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (m : ℕ) {C : ℝ}
    (hC : Analysis.gammaResolventPrefixErrorSum m < C) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) <
      (11783423 / 25000000 : ℝ) * Real.log q + C := by
  rw [gammaResolvent_zeroMass_eq_poissonSum hq hRH hp hne hinv]
  apply
    Analysis.gammaResolvent_weighted_lt_of_variable_prefix
      (fun a : ℚ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((a : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (a : ℝ)) : ℂ) - ρ)))
      (Real.log q) m hC
  intro ab hab
  exact completed_poissonSum_centered_le_resolvent_with_prefix hq hRH hp hne hinv ab hab m

/-- Under primitive nonprincipal individual RH, any certified m-term error sum below C
 gives actual Gamma zero mass below Mlog(q)+C. Use the established global Gamma majorant,
 nonnegative divisor multiplicities and absolute convergence.
 No new kernel-domination hypothesis is introduced. -/
theorem gamma_zeroMass_lt_of_prefix_error {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (m : ℕ) {C : ℝ}
    (hC : Analysis.gammaResolventPrefixErrorSum m < C) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) <
      (11783423 / 25000000 : ℝ) * Real.log q + C := by
  have hΓ := Analysis.norm_Gamma_half_add_I_le_gammaResolvent
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hb (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.gammaResolventMajorant ρ.im := by
    by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
    · simp only [hD, Int.cast_zero, zero_mul, le_refl]
    · have hr :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
          (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
      have he : ρ = (1 / 2 : ℂ) + Complex.I * ρ.im := by
        calc
          ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
          _ = _ := by
            rw [hr]
            norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
            ring
      exact mul_le_mul_of_nonneg_left (by simpa only [← he] using hΓ ρ.im) (hn ρ)
  have hg := summable_completed_gammaResolvent_terms hq hRH hp hne hinv
  have hsum := hg.of_nonneg_of_le (fun ρ ↦ mul_nonneg (hn ρ) (norm_nonneg _)) hb
  exact
    (hsum.tsum_le_tsum hb hg).trans_lt
      (gammaResolvent_zeroMass_lt_of_prefix_error hq hRH hp hne hinv m hC)

/-- Under primitive nonprincipal individual RH and nonprincipal inverse, the actual Gamma
 zero mass is below Mlog(q)+99/5. Apply the variable interface to the sixteen-term certificate.
 This gives a concrete improvement over the eight-term bound. -/
theorem gamma_zeroMass_lt_sixteen {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) <
      (11783423 / 25000000 : ℝ) * Real.log q + 99 / 5 := by
  exact
    gamma_zeroMass_lt_of_prefix_error hq hRH hp hne hinv 16 Analysis.gammaResolvent_sixteen_error_lt

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
