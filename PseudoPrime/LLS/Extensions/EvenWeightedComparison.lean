/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.WeightedComparison
import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.EvenLogWeightedUpper

/-! # The common comparison core with the exact even logarithmic error -/

namespace PseudoPrime.LLS.Extensions

/-- GRH and the two defect bounds construct the common core for an even quadratic
primitive inducing character at `X ≥ 64`. The logarithmic error is kept exact;
the reciprocal estimate supplies the common zero-mass field. This constructor is
independent of the later three-branch numerical comparison. -/
theorem weightedComparisonCore_even_of_grh {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hne : χ ≠ 1) (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X dS dR : ℝ} (hX : 64 ≤ X)
    (hdS : weightedLogDefect χ.primitiveCharacter X ≤ dS)
    (hdR : weightedReciprocalDefect χ.primitiveCharacter X ≤ dR) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| dS dR
      (Analysis.primitiveLogEvenMainError X) := by
  have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor := by
    have h0 := NeZero.pos χ.conductor
    have h1 := AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hp
    omega
  have hi : χ.primitiveCharacter⁻¹ ≠ 1 := inv_ne_one.mpr hp
  refine ⟨hdS, hdR, ?_, ?_⟩
  · have h :=
      primitiveReciprocalRaw_of_grh hf hGRH (DirichletCharacter.primitiveCharacter_isPrimitive χ) hp
        hi hX
    rw [Real.log_div (by exact_mod_cast NeZero.ne χ.conductor) Real.pi_ne_zero]
    linarith only [h]
  · have h :=
      AnalyticNumberTheory.DirichletLFunction.primitiveLogWeightedUpper_of_grh_even_exact hf hGRH
        (DirichletCharacter.primitiveCharacter_isPrimitive χ) hp hi hquad heven hX
    rwa [Real.log_div (by exact_mod_cast NeZero.ne χ.conductor) Real.pi_ne_zero]

end PseudoPrime.LLS.Extensions
