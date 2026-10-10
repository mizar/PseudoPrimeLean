/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ShiftedZeroContribution
public import PseudoPrime.LLS.Extensions.ShiftedGammaContribution

/-!
# Logarithmic formula from integrated residue contributions

Combine the completed-zero and gamma error bounds after the exact residue decomposition.
The decomposition and summable zero mass remain explicit analytic inputs.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For data under individual RH with summable completed-zero mass, gamma shifts having
nonnegative real parts, and `x > 1`, an exact integrated decomposition gives the logarithmic
formula with two real error coefficients bounded by one. Apply the integrated zero and
gamma norm bounds, preserve the signs of the decomposition, and collect the mass terms.
This converts the exact analytic identity to the error form of generalized Lemma 2.5. -/
theorem logValueFormula_of_integrated_contributions (f : GeneralLFunction)
    (hRH : f.RiemannHypothesis) (hm : Summable f.zeroMassTerm) (hκ : ∀ j, 0 ≤ (f.shift j).re)
    {x : ℝ} (hx : 1 < x)
    (hformula :
      Real.log ‖f.L 1‖ =
        (f.logValueSum x).re + f.gammaLogDerivativeAtOne / Real.log x -
            f.zeroMass / (2 * Real.log x) -
            ((∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) / (Real.log x : ℂ)).re +
          (f.gammaLogRemainder x).re) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        Real.log ‖f.L 1‖ =
          (f.logValueSum x).re + f.gammaLogDerivativeAtOne / Real.log x -
              (1 / (2 * Real.log x) + θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) * f.zeroMass +
            2 * (f.degree : ℝ) * θ₂ / (x * (Real.log x) ^ 2) := by
  obtain ⟨θ₁, hθ₁, hz⟩ := integrated_shiftedZeroSum_eq_theta f hRH hm hx
  obtain ⟨θ₂, hθ₂, hg⟩ := gammaLogRemainder_eq_theta f hκ hx
  refine ⟨θ₁, θ₂, hθ₁, hθ₂, ?_⟩
  rw [hformula, hz, hg]
  ring

end PseudoPrime.LLS.Extensions.GeneralLFunction
