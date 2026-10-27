/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrefixPoissonBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaResolventZeroMass

/-! # Gamma zero mass with per-node digamma prefixes

The existing global Gamma majorant and new centered Poisson errors yield additive 199/10.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under primitive nonprincipal individual RH, the signed resolvent zero mass is below
 Mlog(q)+199/10. Use its exact finite Poisson identity and the prefix per-node errors.
 This sharpens the former additive twenty-four without changing the conductor coefficient. -/
theorem gammaResolvent_zeroMass_lt_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) <
      (11783423 / 25000000 : ℝ) * Real.log q + 199 / 10 := by
  rw [gammaResolvent_zeroMass_eq_poissonSum hq hRH hp hne hinv]
  apply
    Analysis.gammaResolvent_weighted_lt_of_prefix_bounds
      (fun a : ℚ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((a : ℝ) / Complex.normSq ((((1 / 2 : ℝ) + (a : ℝ)) : ℂ) - ρ)))
      (Real.log q)
  intro ab hab
  exact completed_poissonSum_centered_le_resolvent_prefix hq hRH hp hne hinv ab hab

/-- Under primitive nonprincipal individual RH and nonprincipal inverse, the actual
 Gamma zero mass is below Mlog(q)+199/10. Nonnegative zero multiplicities and the proved
 global Gamma majorant transfer the prefix resolvent estimate to the convergent Gamma mass.
 This supplies the improved oscillatory zero-sum allowance. -/
theorem gamma_zeroMass_lt_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) <
      (11783423 / 25000000 : ℝ) * Real.log q + 199 / 10 := by
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
  exact (hsum.tsum_le_tsum hb hg).trans_lt (gammaResolvent_zeroMass_lt_prefix hq hRH hp hne hinv)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
