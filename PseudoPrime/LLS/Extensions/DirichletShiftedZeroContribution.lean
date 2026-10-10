/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.DirichletSpecialization
public import PseudoPrime.LLS.Extensions.ShiftedZeroContribution
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation

/-!
# Individual-RH logarithmic zero error for Dirichlet characters

Specialize the general integrated zero contribution and discharge its mass summability
hypothesis for primitive characters. A global shifted explicit formula is not assumed here.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For a primitive nonprincipal character of modulus at least two, individual RH implies
summability of its normalized completed-zero mass. Convert the divisor series to analytic
multiplicities, restrict to zeros, and transfer through the normalization equivalence.
This removes a mass-convergence premise from the logarithmic zero-error estimate. -/
theorem ofDirichletCharacter_summable_zeroMassTerm {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) :
    Summable (ofDirichletCharacter χ).zeroMassTerm := by
  have hdiv :=
    AnalyticNumberTheory.DirichletLFunction.summable_divisor_div_normSq_of_dirichletRH hq hRH hp hne
      (inv_ne_one.mpr hne)
  have hplane :
    Summable (fun z : ℂ ↦ (analyticOrderNatAt χ.completedLFunction z : ℝ) / ‖z‖ ^ 2) := by
    apply hdiv.congr
    intro z
    rw [AnalyticNumberTheory.General.divisor_eq_natCast_analyticOrderNatAt
        (χ.differentiable_completedLFunction hne)]
    simp only [Int.cast_natCast, pow_two, Complex.norm_mul_self_eq_normSq]
  let e : (ofDirichletCharacter χ).Zero ≃ { z : ℂ // χ.completedLFunction z = 0 } :=
    Equiv.subtypeEquivProp (funext fun z ↦ propext (ofDirichletCharacter_completed_eq_zero_iff χ z))
  have hsub := hplane.subtype {z : ℂ | χ.completedLFunction z = 0}
  have he := e.summable_iff.mpr hsub
  apply he.congr
  intro ρ
  change
    (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 =
      (analyticOrderNatAt (ofDirichletCharacter χ).completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2
  rw [ofDirichletCharacter_analyticOrderNatAt_completed χ hne]

/-- For a primitive nonprincipal character of modulus at least two, individual RH and x>1
supply a coefficient |theta|<=1 for the integrated zero term, with scale
2*|primitiveBRe|/(sqrt x*(log x)^2). Apply the general zero-error estimate and prove mass
summability from the character's RH. This is the zero-error coefficient of Lemma 2.5. -/
theorem ofDirichletCharacter_integrated_zero_term_eq_theta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) {x : ℝ} (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        ((∫ σ : ℝ in Set.Ioi 1, (ofDirichletCharacter χ).shiftedZeroSum x σ) /
              (Real.log x : ℂ)).re =
          2 * θ / (Real.sqrt x * (Real.log x) ^ 2) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  obtain ⟨θ, hθ, heq⟩ :=
    integrated_shiftedZeroSum_eq_theta (ofDirichletCharacter χ)
      (ofDirichletCharacter_riemannHypothesis χ hp hne hRH)
      (ofDirichletCharacter_summable_zeroMassTerm χ hq hp hne hRH) hx
  refine ⟨θ, hθ, ?_⟩
  rw [heq, ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH χ hq hp hne hRH]
  ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
