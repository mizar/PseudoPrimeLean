/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaResolventZeroMass

/-! # Convergence of the refined sixth-pole zero mass -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The refined sixth-pole norm is bounded by a single Poisson resolvent at
the same pole distance. Compare the positive denominator with the squared
pole distance. This coarse estimate supplies convergence only; it is not the
sharp differentiated-Poisson coefficient used in the final witness bound. -/
theorem refined_six_pole_norm_le_resolvent (t : ℝ) :
    ‖refinedSixPoleKernel.function (Complex.I * t)‖ ≤
      (27 / 25 : ℝ) / ((27 / 25 : ℝ) ^ 2 + t ^ 2) := by
  rw [refined_six_pole_norm]
  have hd : 0 < (27 / 25 : ℝ) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t)
  apply (div_le_div_iff₀ (pow_pos hd 3) hd).2
  have hs : (27 / 25 : ℝ) ^ 4 ≤ ((27 / 25 : ℝ) ^ 2 + t ^ 2) ^ 2 := by
    nlinarith only [sq_nonneg t, sq_nonneg (t ^ 2)]
  nlinarith only [hs]

/-- For a primitive nonprincipal character under individual RH, with
nonprincipal inverse, the completed-zero series weighted by the actual
refined sixth-pole norm is summable. Dominate it by the existing Poisson
series and use nonnegativity of completed-zero multiplicities. -/
theorem refined_six_pole_zero_summable {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hs :=
    AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hRH hp hne hinv
      (a := 27 / 25) (by norm_num only)
  apply hs.of_nonneg_of_le
  · intro ρ
    exact mul_nonneg (hn ρ) (norm_nonneg _)
  · intro ρ
    exact mul_le_mul_of_nonneg_left (refined_six_pole_norm_le_resolvent ρ.im) (hn ρ)

end PseudoPrime.PrimeTestBounds.MillerRabin
