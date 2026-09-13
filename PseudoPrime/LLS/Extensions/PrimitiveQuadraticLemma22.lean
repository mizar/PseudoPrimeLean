/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Theorem11S1FullLevel
import PseudoPrime.LLS.Lemma22
import PseudoPrime.LLS.Extensions.PrimitiveQuadraticLemma23
import PseudoPrime.LLS.Extensions.PrimitiveQuadraticLogContour
import PseudoPrime.LLS.RiemannLogResidueBound
import PseudoPrime.LLS.RiemannReciprocalResidueBound

/-!
# Quadratic full-level assembly for the logarithmic estimate

Connects the quadratic logarithmic estimate to `LLSPart1PrimitiveWeightedUpperAt` and combines
it with the reciprocal estimate and the logarithmic conductor absorption.  The resulting bound for
the original character is expressed in terms of the level alone.  The contour-dependent results
are kept in this extension module to avoid an import cycle in the basic lemma modules.

The resulting bound is sharper than the coarser level bound in `Numerics.lean`; a bridge theorem
relates the two so that the existing numerical comparison can be reused.
-/

namespace PseudoPrime.LLS.Extensions

/--
Input/assumptions: a level-`q` character with `q ≥ 3000`, `χ ≠ 1`, GRH, and a quadratic primitive
inducing character.
Conclusion: `LLSPart1PrimitiveWeightedUpperAt χ
|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|`.
Content: `y := llsTheorem11S1RadiusRoot q > 8` (`eight_lt_llsTheorem11S1RadiusRoot`) gives `x := y²
≥ 64` and
`√x = y`; `χ.primitiveCharacter.IsPrimitive`, `χ.primitiveCharacter ≠ 1`,
`χ.primitiveCharacter⁻¹ ≠ 1` (from `hquad.inv`), and `2 ≤ χ.conductor` (from `χ.primitiveCharacter
≠ 1`) feed `primitiveQuadraticLogWeightedUpper` directly; `Real.log_div` matches its
`(1/2)(log N - log π) log x` term to `LLSPart1PrimitiveWeightedUpperAt`'s `log(d/π) * log x / 2`.
Role: connects the quadratic logarithmic estimate to the level-indexed API.
-/
theorem llsPart1PrimitiveWeightedUpperAt_of_grh_quadratic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hquad : χ.primitiveCharacter.IsQuadratic) :
    LLSPart1PrimitiveWeightedUpperAt χ
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| := by
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hinv : χ.primitiveCharacter⁻¹ ≠ 1 := by
    rw [hquad.inv]; exact hprimne
  have hN2 : 2 ≤ χ.conductor := by
    have hN1 : χ.conductor ≠ 1 :=
      AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
        hprimne
    have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
    omega
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := by linarith
  have hx64 : (64 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by
    have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 8 by norm_num only) hy.le
    calc
      (64 : ℝ) = 8 * 8 := by norm_num only
      _ ≤ llsTheorem11S1RadiusRoot q * llsTheorem11S1RadiusRoot q := hsq
      _ = (llsTheorem11S1RadiusRoot q) ^ 2 := by ring
  have hsqrt : Real.sqrt ((llsTheorem11S1RadiusRoot q) ^ 2) = llsTheorem11S1RadiusRoot q := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hraw := primitiveQuadraticLogWeightedUpper hN2 hGRH hprimitive hprimne hinv hquad hx64
  rw [hsqrt] at hraw
  have hlogdiv : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast χ.conductor_ne_zero) Real.pi_ne_zero
  unfold LLSPart1PrimitiveWeightedUpperAt
  rw [hlogdiv]
  linarith [hraw]


open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Input/assumptions: LLS Lemma 2.4's Riemann reciprocal lower bound, a level-`q` character with
`q ≥ 3000`, `χ ≠ 1`, no-small-prime, GRH, and a quadratic primitive inducing character.
Conclusion: `Re S(X, χ) ≤ llsPart1PrimitiveFullLevelUpperBound q`, where
`X = (llsTheorem11S1RadiusRoot q)²`.
Content: combines Lemma 2.2's quadratic instance
(`llsPart1PrimitiveWeightedUpperAt_of_grh_quadratic`, bounding `Re S(X, χ̃)`), the analytic
estimate's completed
reciprocal full-level zero-mass bound (`llsPart1PrimitiveZeroMassFullLevelRawAt_of_grh_quadratic`,
already at `q`-level via the conductor estimate, bounding `b`), the exact primitive/level
logarithmic identity
(`Arithmetic.characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection`),
and the conductor estimate's exact
logarithmic conductor absorption
(`PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveLogConductorAbsorption`, the generic version,
which needs no quadratic hypothesis, moving the level-change correction from a free-standing term
into the conductor term already present in Lemma 2.2's bound). Since Lemma 2.2's coefficient
`A(X) = 2y + 2 + log X ≥ 0`, multiplying the
`q`-level zero-mass bound by `A(X) / (1 - 1/y)²` and chaining the three facts eliminates both the
conductor and the level-change correction, leaving a bound purely in `q`.
Role: the quadratic full-level upper bound for the original character, before coarsening.
-/
theorem characterLogWeightedSum_re_le_fullLevel_of_grh_quadratic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hquad : χ.primitiveCharacter.IsQuadratic) (h24 : LLSRiemannReciprocalLowerBound)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re ≤
      llsPart1PrimitiveFullLevelUpperBound q := by
  have hweighted := llsPart1PrimitiveWeightedUpperAt_of_grh_quadratic χ hq hne hGRH hquad
  unfold LLSPart1PrimitiveWeightedUpperAt at hweighted
  have hzeromass :=
    llsPart1PrimitiveZeroMassFullLevelRawAt_of_grh_quadratic χ hq hne hGRH hquad h24 hsmall
  unfold LLSPart1PrimitiveZeroMassFullLevelRawAt at hzeromass
  have hexact :=
    characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ
  have hy8 : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := by linarith
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact
      ⟨χ.conductor_ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level⟩
  have hx2 : (2 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by
    have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 8 by norm_num only) hy8.le
    calc
      (2 : ℝ) ≤ 64 := by norm_num only
      _ = 8 * 8 := by norm_num only
      _ ≤ llsTheorem11S1RadiusRoot q * llsTheorem11S1RadiusRoot q := hsq
      _ = (llsTheorem11S1RadiusRoot q) ^ 2 := by ring
  have habsorb :=
    primitiveLogConductorAbsorption
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ hx2 hqd
  have hlogxnn : (0 : ℝ) ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) :=
    Real.log_nonneg (le_trans (by norm_num only) hx2)
  have hC22nonneg :
    (0 : ℝ) ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    have hy_nonneg : (0 : ℝ) ≤ llsTheorem11S1RadiusRoot q := hypos.le
    have hfirst : (0 : ℝ) ≤ 2 * llsTheorem11S1RadiusRoot q + 2 :=
      add_nonneg (mul_nonneg (by norm_num only) hy_nonneg) (by norm_num only)
    exact add_nonneg hfirst hlogxnn
  have hinv2pos : (0 : ℝ) < (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 := by
    have : (0 : ℝ) < 1 - 1 / llsTheorem11S1RadiusRoot q := by
      rw [sub_pos, div_lt_one hypos]; linarith
    positivity
  have hlogdconddiv :
    Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast χ.conductor_ne_zero) Real.pi_ne_zero
  have hlogqdiv : Real.log ((q : ℝ) / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast (NeZero.ne q)) Real.pi_ne_zero
  rw [hlogqdiv] at hzeromass
  have hbdiv :
    |primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4) /
        (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 :=
    (le_div_iff₀ hinv2pos).mpr
      (by
        rw [mul_comm]
        exact hzeromass)
  have hmul := mul_le_mul_of_nonneg_left hbdiv hC22nonneg
  have hmuleq :
    (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) *
        ((1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
            llsAuxiliaryTerm q -
            1 / 4) /
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2) =
      (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2)) /
          (1 - 1 / llsTheorem11S1RadiusRoot q) ^ 2 *
        (1 / 2 * (1 - 1 / (llsTheorem11S1RadiusRoot q) ^ 2) * (Real.log q - Real.log Real.pi) -
          llsAuxiliaryTerm q -
          1 / 4) := by
    ring
  rw [hmuleq] at hmul
  unfold llsPart1PrimitiveFullLevelUpperBound
  rw [hlogdconddiv] at hweighted
  linarith [hweighted, hexact, habsorb, hmul]


/--
Input/assumptions: LLS Lemma 2.4's Riemann reciprocal lower bound, a level-`q` character with
`q ≥ 3000`, `χ ≠ 1`, no-small-prime, GRH, and a quadratic primitive inducing character.
Conclusion: `Re S(X, χ) ≤ llsTheorem11S1UpperBound q`.
Content: chains `characterLogWeightedSum_re_le_fullLevel_of_grh_quadratic`,
`llsPart1PrimitiveFullLevelUpperBound_le_fullLevel`,
`llsPart1FullLevelUpperBound_le_intermediate`, and `llsPart1IntermediateUpperBound_le_upper`
(the first comparison is proved above; the final two are in `LLS/Numerics.lean`).
Role: supplies the analytic upper bound used by the final contradiction theorem.
-/
theorem characterLogWeightedSum_re_le_part1Upper_of_grh_quadratic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hquad : χ.primitiveCharacter.IsQuadratic) (h24 : LLSRiemannReciprocalLowerBound)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((llsTheorem11S1RadiusRoot q) ^ 2) χ).re ≤
      llsTheorem11S1UpperBound q :=
  (characterLogWeightedSum_re_le_fullLevel_of_grh_quadratic χ hq hne hGRH hquad h24 hsmall).trans
    ((llsPart1PrimitiveFullLevelUpperBound_le_fullLevel hq).trans
      ((llsPart1FullLevelUpperBound_le_intermediate hq).trans
        (llsPart1IntermediateUpperBound_le_upper hq)))

/--
The quadratic specialization of `llsTheorem11S1Character`: every nontrivial level-`q` character
whose
primitive inducing character is quadratic, with `q ≥ 3000`, has a prime `ℓ ∤ q` with `χ ℓ ≠ 1`
at most the LLS search radius.
Matches `llsTheorem11S1Character` exactly except for the added `χ.primitiveCharacter.IsQuadratic`
hypothesis,
needed because the preceding estimates are stated for quadratic characters.
-/
def llsTheorem11S1QuadraticCharacter : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      χ.primitiveCharacter.IsQuadratic →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ℓ ∣ q ∧ χ ℓ ≠ 1 ∧ (ℓ : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2

/--
Input/assumptions: GRH, LLS Lemma 2.1's Riemann weighted lower bound, and LLS Lemma 2.4's Riemann
reciprocal lower bound.
Conclusion: `llsTheorem11S1QuadraticCharacter`.
Content: the same contradiction argument as `llsTheorem11S1Character_of_bounds`, specialized to
quadratic
characters: a hypothetical counterexample gives `llsTheorem11S1NoSmallPrime χ`,
which is combined with the Riemann weighted lower-bound theorem and
`characterLogWeightedSum_re_le_part1Upper_of_grh_quadratic` to sandwich `Re S(X, χ)` between
`llsTheorem11S1LowerBound q` and `llsTheorem11S1UpperBound q`, contradicting
`llsTheorem11S1NumericalSeparation`.
Role: quadratic-specialized assembly theorem parameterized by the two Riemann lower bounds.
The final GRH theorem below discharges both interfaces using the completed Riemann residue
proofs.
-/
theorem llsTheorem11S1QuadraticCharacter_of_grh_and_riemann_bounds
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (h21 : LLSRiemannWeightedLowerBound) (h24 : LLSRiemannReciprocalLowerBound) :
    llsTheorem11S1QuadraticCharacter := by
  intro q _ χ hq hne hquad
  by_contra hcounterexample
  have hsmall : llsTheorem11S1NoSmallPrime χ := by
    intro ℓ hℓprime hℓndvd hℓle
    by_contra hℓvalue
    exact hcounterexample ⟨ℓ, hℓprime, hℓndvd, hℓvalue, hℓle⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hlower := llsPart1WeightedLowerBounds_of_riemann h21 q χ hq hne hsmall
  have hupper :=
    characterLogWeightedSum_re_le_part1Upper_of_grh_quadratic χ hq hne hGRH hquad h24 hsmall
  exact (not_le_of_gt (llsPart1NumericalSeparation q hq)) (hlower.trans hupper)

/--
Input/assumptions: GRH.
Conclusion: `llsTheorem11S1QuadraticCharacter`.
Content: both Riemann-side inputs of `llsTheorem11S1QuadraticCharacter_of_grh_and_riemann_bounds`
are proved from RH alone (`llsRiemannWeightedLowerBound_of_riemannHypothesis`
in `RiemannLogResidueBound.lean`; `llsRiemannReciprocalLowerBound_of_riemannHypothesis`
`RiemannReciprocalResidueBound.lean`), so this composes them using `hGRH.riemann`.
Role: the public quadratic-specialized goal, resting on GRH alone.
-/
theorem llsTheorem11S1QuadraticCharacter_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    llsTheorem11S1QuadraticCharacter :=
  llsTheorem11S1QuadraticCharacter_of_grh_and_riemann_bounds hGRH
    (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
    (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)

end PseudoPrime.LLS.Extensions
