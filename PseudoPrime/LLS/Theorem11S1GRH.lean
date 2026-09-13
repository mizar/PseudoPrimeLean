/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.ExplicitFormula
import PseudoPrime.LLS.Theorem11S1Estimates
import PseudoPrime.LLS.Lemma23
import PseudoPrime.LLS.Theorem11S1Subgroup
import PseudoPrime.LLS.RiemannLogResidueBound
import PseudoPrime.LLS.RiemannReciprocalResidueBound

/-!
# Assembly of the analytic core for LLS Theorem 1.1

This file is an interface/assembly layer for the generic `llsTheorem11S1Character` route.  It
records three
analytic inputs and composes them with the finite and numerical layers. The final GRH theorem
supplies the general S1 bound used by `elementary_formula`.
-/

namespace PseudoPrime.LLS

/-- The analytic-core interface for the generic character version of LLS Theorem 1.1.

The first two fields are the Riemann logarithmic and reciprocal vertical-integral lower bounds.
The final field is the primitive completed-`L` shared-witness estimate. Once these are proved from
`PseudoPrime.AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis`,
the existing finite and numerical layers yield `llsTheorem11S1Character`. -/
structure LLSAnalyticCore : Prop where
  /-- The logarithmic Riemann vertical-integral lower bound. -/
  riemannLog : LLSRiemannLogVerticalIntegralLowerBound
  /-- The reciprocal Riemann vertical-integral lower bound. -/
  riemannReciprocal : LLSRiemannReciprocalVerticalIntegralLowerBound
  /-- The primitive completed-`L` raw shared-witness estimate. -/
  primitiveRaw : LLSPart1PrimitiveRawCoreBounds

/-- The analytic core supplies the Riemann weighted lower bound of LLS Lemma 2.1.

The proof uses the completed Mellin/vertical-integral identification in `ExplicitFormula.lean`. -/
theorem LLSAnalyticCore.riemannWeightedLowerBound (hcore : LLSAnalyticCore) :
    LLSRiemannWeightedLowerBound :=
  llsRiemannWeightedLowerBound_of_verticalIntegralLowerBound hcore.riemannLog

/-- The analytic core supplies the reciprocal Riemann lower bound of LLS Lemma 2.4.

The proof uses `llsRiemannReciprocalExplicitLowerBound_of_verticalIntegralLowerBound`
and `llsRiemannReciprocalLowerBound_of_explicit_analytic`. -/
theorem LLSAnalyticCore.riemannReciprocalLowerBound (hcore : LLSAnalyticCore) :
    LLSRiemannReciprocalLowerBound :=
  llsRiemannReciprocalLowerBound_of_explicit_analytic
    (llsRiemannReciprocalExplicitLowerBound_of_verticalIntegralLowerBound hcore.riemannReciprocal)

/-- The analytic core proves the character-specialized LLS Theorem 1.1.

It converts the logarithmic Riemann vertical bound to a finite weighted lower bound, then combines
it with `primitiveRaw` through the algebraic and numerical reductions. The `riemannReciprocal`
field is not needed by this theorem. -/
theorem LLSAnalyticCore.llsTheorem11S1Character (hcore : LLSAnalyticCore) :
    llsTheorem11S1Character := by
  exact llsTheorem11S1Character_of_riemann_and_primitive_raw
    hcore.riemannWeightedLowerBound hcore.primitiveRaw

/-!
The generic exact full-level route supplies the existing Part 1 analytic-bounds interface.
This bridge bypasses the coarse quotient branch: the lower side remains the established
Riemann weighted lower bound, while the upper side is the exact full-level chain.
-/

theorem llsPart1AnalyticBounds_of_grh_generic (h21 : LLSRiemannWeightedLowerBound)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) : llsTheorem11S1AnalyticBounds := by
  intro q _ χ hq hχ hsmall
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  refine
    ⟨(AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re,
      ?_, ?_⟩
  · exact (llsPart1WeightedLowerBounds_of_riemann h21) q χ hq hχ hsmall
  · exact characterLogWeightedSum_re_le_upper_of_grh_generic χ hq hχ hGRH h24 hsmall

/- The generic analytic Part 1 input is consumed by the existing numerical separation theorem. -/
theorem llsTheorem11S1Character_of_grh_generic_analytic (h21 : LLSRiemannWeightedLowerBound)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) : llsTheorem11S1Character := by
  exact
    llsTheorem11S1Character_of_bounds (llsPart1AnalyticBounds_of_grh_generic h21 hGRH h24)
      llsPart1NumericalSeparation

/-!
Intermediate generic full-level core.  This public interface retains the exact level-change
reciprocal lower bound and absorbed zero-mass estimate with an explicit shared witness.
-/

def LLSPart1PrimitiveFullLevelCoreBounds : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      ∃ b : ℝ,
        0 ≤ b ∧
          LLSPart1PrimitiveWeightedUpperAt χ b ∧
          LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt χ ∧
          LLSPart1PrimitiveZeroMassFullLevelRawAt χ b

/-- The generic estimates construct the full-level core with witness
`|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe|`. -/
theorem llsPart1PrimitiveFullLevelCoreBounds_of_grh_generic
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h24 : LLSRiemannReciprocalLowerBound) : LLSPart1PrimitiveFullLevelCoreBounds := by
  intro q _ χ hq hne hsmall
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  refine
    ⟨|AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|,
      abs_nonneg _, ?_, ?_, ?_⟩
  · exact llsPart1PrimitiveWeightedUpperAt_of_grh_generic χ hq hne hGRH
  · exact llsPart1PrimitiveReciprocalLowerWithLevelChangeAt_of_riemann h24 χ hq hsmall
  · exact llsPart1PrimitiveZeroMassFullLevelRawAt_of_grh_generic χ hq hne hGRH h24 hsmall

/-- GRH implies the nontrivial-character S1 bound. The proof obtains the Riemann lower
bounds from `hGRH.riemann`, combines them with the general primitive-character upper
estimates, and applies numerical separation. This supplies the subgroup and Jacobi bounds. -/
theorem llsTheorem11S1Character_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) : llsTheorem11S1Character := by
  exact
    llsTheorem11S1Character_of_grh_generic_analytic
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann) hGRH
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)

/-- GRH gives the proper-subgroup S1 bound through the general character theorem.
The quotient-character construction supplies separation for every proper subgroup;
no quadraticity or additional analytic interface is assumed. -/
theorem llsTheorem11S1_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) : llsTheorem11S1 := by
  exact llsTheorem11S1_of_character (llsTheorem11S1Character_of_grh hGRH)

/-- Under GRH, the least prime outside any proper subgroup at level `q ≥ 3000`
satisfies the S1 bound. The least-prime conclusion uses the unbounded admissibility
predicate, so minimality holds among all primes outside the subgroup. -/
theorem exists_least_prime_outside_subgroup_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {q : ℕ} [NeZero q] (hq : 3000 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p, PrimeOutsideSubgroup q H p ∧
      (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 ∧
      ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact exists_least_prime_outside_subgroup_of_s1 (llsTheorem11S1_of_grh hGRH) hq H hH

end PseudoPrime.LLS
