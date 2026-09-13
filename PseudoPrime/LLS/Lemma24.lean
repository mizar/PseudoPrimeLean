/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.EulerMascheroniBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
import PseudoPrime.LLS.Lemma23
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroMultiplicity

/-!
# The Riemann reciprocal explicit-formula interface

This file separates the analytic explicit formula behind LLS Lemma 2.4 from the numerical
estimate that replaces its remainder by `-8 / 5`.  Their conjunction gives exactly the Riemann
reciprocal lower bound `LLSRiemannReciprocalLowerBound` consumed by `Lemma23.lean`.
-/

namespace PseudoPrime.LLS

/--
The lower-bound form of the Riemann explicit formula in LLS Lemma 2.4.

Under RH, the nontrivial-zero contribution is bounded below by
`-2 * |B| / sqrt x`.  The remaining terms are written with the same normalization as the v3
source, lines 550--568.
-/
def LLSRiemannReciprocalExplicitLowerBound : Prop :=
  ∀ x : ℝ,
    1 < x →
      Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
          AnalyticNumberTheory.RiemannZeta.riemannReciprocalTrivialZeroSeries x -
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x ≤
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum x

/-- The elementary uniform remainder estimate that produces the constant `8 / 5`. -/
def LLSRiemannReciprocalRemainderBound : Prop :=
  ∀ x : ℝ,
    2 ≤ x →
      -(8 / 5 : ℝ) ≤
        -(1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
          AnalyticNumberTheory.RiemannZeta.riemannReciprocalTrivialZeroSeries x -
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x

/-- The reciprocal Riemann remainder is uniformly bounded below by `-8 / 5`. -/
theorem llsRiemannReciprocalRemainderBound : LLSRiemannReciprocalRemainderBound := by
  intro x hx
  have hxpos : 0 < x := by linarith
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have htail :=
    (AnalyticNumberTheory.RiemannZeta.riemannReciprocalTrivialZeroSeries_le_geometric
          hx).trans
      (Analysis.geometricTail_le_one_div_eighteen_mul hx)
  have hzeroNumerator :
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 10 : ℝ) := by
    nlinarith [AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths]
  have hzero :
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x ≤
      3 / (10 * Real.sqrt x) := by
    calc
      _ ≤ (3 / 10 : ℝ) / Real.sqrt x := (div_le_div_iff_of_pos_right hsqrt).2 hzeroNumerator
      _ = 3 / (10 * Real.sqrt x) := by ring
  have hsqrtTradeoff := Analysis.three_tenths_div_sqrt_le hx
  have hlog : (3 / 2 : ℝ) / x ≤ Real.log (2 * Real.pi) / x :=
    div_le_div_of_nonneg_right Analysis.three_halves_le_log_two_pi hxpos.le
  have hcost :
    AnalyticNumberTheory.RiemannZeta.riemannReciprocalTrivialZeroSeries x +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x ≤
      1 / 50 + Real.log (2 * Real.pi) / x := by
    have hreciprocal : (1 : ℝ) / (18 * x) + 9 / (8 * x) ≤ (3 / 2) / x := by
      field_simp [hxpos.ne']
      norm_num only
    linarith
  nlinarith [Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths]

/-- The explicit-formula lower bound and its remainder estimate imply the reciprocal lower bound. -/
theorem llsRiemannReciprocalLowerBound_of_explicit
    (hexplicit : LLSRiemannReciprocalExplicitLowerBound)
    (hremainder : LLSRiemannReciprocalRemainderBound) : LLSRiemannReciprocalLowerBound := by
  intro x hx
  have hlower := hexplicit x (by linarith)
  have herror := hremainder x hx
  linarith

/-- The explicit-formula lower bound alone now implies the reciprocal Riemann estimate. -/
theorem llsRiemannReciprocalLowerBound_of_explicit_analytic
    (hexplicit : LLSRiemannReciprocalExplicitLowerBound) : LLSRiemannReciprocalLowerBound :=
  llsRiemannReciprocalLowerBound_of_explicit hexplicit llsRiemannReciprocalRemainderBound

/-- The staged Riemann inputs supply the Part 1 reciprocal bound under equal prime support. -/
theorem llsPart1PrimitiveReciprocalLowerAt_of_explicit_of_conductorPrimeSupport
    (hexplicit : LLSRiemannReciprocalExplicitLowerBound)
    (hremainder : LLSRiemannReciprocalRemainderBound) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hsmall : llsTheorem11S1NoSmallPrime χ)
    (hsupport : AnalyticNumberTheory.Arithmetic.ConductorPrimeSupport χ) :
    LLSPart1PrimitiveReciprocalLowerAt χ :=
  llsPart1PrimitiveReciprocalLowerAt_of_riemann_of_conductorPrimeSupport
    (llsRiemannReciprocalLowerBound_of_explicit hexplicit hremainder) χ hq hsmall hsupport

/--
The explicit Riemann reciprocal formula supplies the conductor-safe lower input for an arbitrary
Part 1 character.

The complementary quotient correction remains visible in the conclusion, so no conductor-prime-
support assumption is introduced at this stage.
-/
theorem llsPart1PrimitiveReciprocalLowerAtWithQuotient_of_explicit
    (hexplicit : LLSRiemannReciprocalExplicitLowerBound)
    (hremainder : LLSRiemannReciprocalRemainderBound) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hsmall : llsTheorem11S1NoSmallPrime χ) :
    LLSPart1PrimitiveReciprocalLowerAtWithQuotient χ :=
  llsPart1PrimitiveReciprocalLowerAtWithQuotient_of_riemann
    (llsRiemannReciprocalLowerBound_of_explicit hexplicit hremainder) χ hq hsmall

end PseudoPrime.LLS
