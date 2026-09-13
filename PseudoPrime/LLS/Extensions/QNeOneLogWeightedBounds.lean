/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.PrimitiveLogWeightedBounds
import PseudoPrime.LLS.PrimitiveLogResidueLedger
import PseudoPrime.LLS.RiemannReciprocalResidueBound
import PseudoPrime.Analysis.LogarithmicRatios
import PseudoPrime.LLS.Extensions.QNeOneNumerics
import PseudoPrime.LLS.Extensions.QNeOneWeightedComparisonInputs
import PseudoPrime.Analysis.LogarithmicMainTerms
import PseudoPrime.Analysis.QNeOneElementaryBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.EvenLogWeightedUpper
import PseudoPrime.Analysis.LogarithmicConstants
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues
import PseudoPrime.Analysis.ElementaryBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogExplicitFormula
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
import PseudoPrime.LLS.Lemma22
import PseudoPrime.LLS.Extensions.PrimitiveQuadraticReciprocalContour
import PseudoPrime.LLS.Extensions.PrimitiveQuadraticLemma23
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.LLS.Numerics

/-!
# Quadratic logarithmic bounds and QNeOne comparisons

This module retains the quadratic contour estimates and assembles the three corrected
quadratic branches used by `QNeOneConcrete.lean`. General S1 estimates live in
`LLS/Theorem11S1Estimates.lean`.
-/

namespace PseudoPrime.LLS.Extensions

/-- The Riemann lower envelope with the half-square defect dominates the common
quadratic lower bound for `y ≥ 8`. The certified zero mass and logarithmic constants
supply the two coefficient comparisons used by all three core consumers. -/
theorem qNeOneAnalyticLowerBound_le_riemann_lower {y : ℝ} (hy : 8 ≤ y) :
    qNeOneAnalyticLowerBound y ≤
      riemannLogLowerAt (y ^ 2) - (Real.log (y ^ 2)) ^ 2 / 2 := by
  have hm := mul_le_mul_of_nonneg_right
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
    (show 0 ≤ y + 1 by linarith only [hy])
  have hl := mul_le_mul_of_nonneg_right
    (Analysis.log_two_mul_pi_lt.le.trans (show (1839 / 1000 : ℝ) ≤ 2 by norm_num only))
    (Real.log_nonneg (show 1 ≤ y by linarith only [hy]))
  rw [qNeOneAnalyticLowerBound, riemannLogLowerAt,
    Real.sqrt_sq (by linarith only [hy]), Real.log_pow]
  norm_num only
  nlinarith only [hm, hl]


/-!
The quadratic residue-ledger bound is transferred through the generic boundary limit.
The version without a quadraticity hypothesis is
`re_characterLogWeightedSum_sub_leftVertical_le_generic_of_grh` in `PrimitiveLogWeightedBounds`.
-/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem re_characterLogWeightedSum_sub_leftVertical_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (characterLogWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I)).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have htend :=
    tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh
      hN2 hGRH hprimitive hne hinv hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletLogContourKernel x χ)
              (primitiveHeightSeqLowerCorner_of_grh
                hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner_of_grh
                hN2 hGRH hprimitive hne hinv k)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) *
              |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards with k
    have hid :=
      dirichletLogFiniteContourIdentity_heightSeq_normalized_of_grh
        hN2 hGRH hprimitive hne hinv (lt_of_lt_of_le zero_lt_one hx1) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq_of_grh
        hN2 hGRH hprimitive hne hinv A k hA
    have hbound :=
      re_sum_llsPrimitiveLogResidueAt_le hN2 hGRH hprimitive hne hinv hquad hx (z :=
        primitiveHeightSeqLowerCorner_of_grh hN2
          hGRH hprimitive hne hinv A k)
        (w :=
        primitiveHeightSeqUpperCorner_of_grh hN2
          hGRH hprimitive hne hinv k)
        h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletLogContourKernel x χ
              (((primitiveReciprocalLeftRe A :
                    ℝ) :
                  ℂ) +
                (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/-!
Input/assumptions: the same arithmetic hypotheses as the residue ledger and `x ≥ 64`.
Conclusion: the left-vertical term is removed by `A → ∞`, yielding the logarithmic raw bound.
Content: transfer the fixed-`A` inequality through the generic whole-line left-edge limit and
continuity of the real part.
Role: completes the logarithmic contour-to-raw-bound passage available from the current ledger.
-/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
private theorem primitiveQuadraticLogWeightedUpperLegacy {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) :
    (characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
  have htend :=
    tendsto_dirichletLogContourKernel_leftVertical_integral_atTop
      hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re)
      Filter.atTop
      (nhds
        ((characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) *
              |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterLogWeightedSum_sub_leftVertical_le_of_grh hN2 hGRH hprimitive hne hinv hquad hx A
        hA
  exact le_of_tendsto htendScaled hev

/-!
Input/assumptions: a nontrivial level character with quadratic primitive character, GRH, a
Riemann weighted lower bound, `y ≥ 8`, and the branch `χ̃(2) = 0` at `X = y²`.
Conclusion: the corrected logarithmic lower bound and the generic logarithmic contour upper
bound form one common lower/upper interface for the same primitive character and witness.
Content: apply the corrected lower theorem and the generic upper theorem, then rewrite
`sqrt (y²) = y` and `log (y²) = 2 log y`.
Role: supplies the zero-branch bounds before conductor substitution. Evenness is not required.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
          (2 * Real.log y) ^ 2 / 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hinv : χ.primitiveCharacter⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hprimne
  have hN2 : 2 ≤ χ.conductor := by
    have hN1 : χ.conductor ≠ 1 :=
      AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
        hprimne
    have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
    omega
  have hlower :=
    characterLogWeightedSum_re_ge_riemann_lower_sub_half_log_sq_of_eq_zero (y ^ 2) χ hriemann
      ((by norm_num only : (2 : ℝ) ≤ 64).trans (Analysis.sq_ge_64_of_ge_8 hy)) hodd h2
  have hupper :=
    primitiveGenericLogWeightedUpper_of_grh_generic (χ := χ.primitiveCharacter) hN2 hGRH hprimitive
      hprimne hinv hx64
  rw [hsqrt, hlogsq] at hlower hupper
  exact ⟨hlower, hupper⟩

/-!
Input/assumptions: the same quadratic GRH and weighted Riemann hypotheses, with the c=1
Q-ne-one branch at `X = y²`.
Conclusion: the corrected logarithmic lower bound and generic contour upper bound are paired.
Content: the c=1 correction vanishes, but the lower-bound API retains the weaker
`(log X)^2 / 2` loss shared with the zero branch.
Proof: apply the c=1 lower theorem and the unchanged generic upper theorem, then normalize `y²`.
Role: the analytic interface before conductor substitution and elimination of `|Re B|`.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
          (2 * Real.log y) ^ 2 / 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hinv : χ.primitiveCharacter⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hprimne
  have hN2 : 2 ≤ χ.conductor := by
    have hN1 : χ.conductor ≠ 1 :=
      AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
        hprimne
    have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
    omega
  have hlower :=
    characterLogWeightedSum_re_ge_riemann_lower_sub_half_log_sq_of_eq_one (y ^ 2) χ hquad hriemann
      ((by norm_num only : (2 : ℝ) ≤ 64).trans (Analysis.sq_ge_64_of_ge_8 hy)) hodd h2
  have hupper :=
    primitiveGenericLogWeightedUpper_of_grh_generic (χ := χ.primitiveCharacter) hN2 hGRH hprimitive
      hprimne hinv hx64
  rw [hsqrt, hlogsq] at hlower hupper
  exact ⟨hlower, hupper⟩

/-!
The conductor-traded form used by the numerical stage.  It consumes `log D ≤ y` and the existing
coarse zero-mass estimate, so the remaining upper bound depends only on `y` and the same `B`
witness.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_traded {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
          2 * (Real.log y) ^ 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hbase :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch χ hne hquad hGRH hy hriemann hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans hy)
  have hmass : AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 20 : ℝ) :=
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
  have hleft :
    y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
        2 * (Real.log y) ^ 2 ≤
      y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
        (2 * Real.log y) ^ 2 / 2 := by
    have hy_nonneg : (0 : ℝ) ≤ y := le_trans (by norm_num only) hy
    have hy1 : (0 : ℝ) ≤ y + 1 := add_nonneg hy_nonneg (by norm_num only)
    have hcoef : 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 10 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 2 by norm_num only)
      calc
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ 2 * (3 / 20 : ℝ) := hmul
        _ = (3 / 10 : ℝ) := by ring
    have hprod := mul_le_mul_of_nonneg_right hcoef hy1
    calc
      _ =
          y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
            2 * (Real.log y) ^ 2 :=
        by ring
      _ ≤
          y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 -
            2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
            2 * (Real.log y) ^ 2 :=
        by
        have hsub :=
          sub_le_sub_left hprod
            (y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - 2 * (Real.log y) ^ 2)
        calc
          _ =
              y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - 2 * (Real.log y) ^ 2 -
                (3 / 10 : ℝ) * (y + 1) :=
            by ring
          _ ≤
              y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - 2 * (Real.log y) ^ 2 -
                2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) :=
            hsub
          _ = _ := by ring
      _ = _ := by ring
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 ≤
      (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 := by
    gcongr
  constructor
  · exact hleft.trans hbase.1
  · apply hbase.2.trans
    calc
      _ =
          ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) +
            ((2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter|) :=
        by ring
      _ ≤
          ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) +
            ((2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter|) :=
        add_le_add_left hright _
      _ = _ := by ring

/-!
Input/assumptions: the zero branch at `X = y²`, GRH, the Riemann lower bound, and
`log conductor ≤ y + log 4`.
Conclusion: the common lower bound is paired with the logarithmic upper bound before
the new `Ẽ₀` refinement, while retaining the `log 4` conductor penalty explicitly.
Content: specialize the existing square-radius bridge and multiply the conductor inequality
by the nonnegative `log y` factor.
Role: supplies the c=0 bound with the explicit conductor penalty for the B-bound adapter.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_log_four {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hbase :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch χ hne hquad hGRH hy hriemann hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hmass : AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 20 : ℝ) :=
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
  have hleft :
    qNeOneAnalyticLowerBound y ≤
      y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
        (2 * Real.log y) ^ 2 / 2 := by
    have hprod : 2 * Real.log (2 * Real.pi) * Real.log y ≤ 4 * Real.log y := by
      have :=
        mul_le_mul_of_nonneg_right
          (show 2 * Real.log (2 * Real.pi) ≤ 4 by
            calc
              2 * Real.log (2 * Real.pi) ≤ 2 * (1839 / 1000 : ℝ) :=
                mul_le_mul_of_nonneg_left Analysis.log_two_mul_pi_lt.le
                  (by norm_num only)
              _ ≤ 4 := by norm_num only)
          hlogy
      exact this
    have hy1 : (0 : ℝ) ≤ y + 1 := add_nonneg (le_trans (by norm_num only) hy) (by norm_num only)
    have hmass2 :
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ 2 * (3 / 20 : ℝ) :=
      mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 2 by norm_num only)
    have hmassprod := mul_le_mul_of_nonneg_right hmass2 hy1
    unfold qNeOneAnalyticLowerBound
    have hlog := neg_le_neg hprod
    have hmass' :
      -(3 / 10 : ℝ) * (y + 1) ≤
        -2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) := by
      calc
        -(3 / 10 : ℝ) * (y + 1) = -(2 * (3 / 20 : ℝ) * (y + 1)) := by ring
        _ ≤ -(2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1)) :=
          neg_le_neg hmassprod
        _ = _ := by ring
    calc
      _ = (y ^ 2 - 1 - 2 * (Real.log y) ^ 2) - (3 / 10 : ℝ) * (y + 1) - 4 * Real.log y := by ring
      _ ≤
          (y ^ 2 - 1 - 2 * (Real.log y) ^ 2) -
            2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
            2 * Real.log (2 * Real.pi) * Real.log y :=
        by
        have hboth := add_le_add hmass' hlog
        calc
          _ = (y ^ 2 - 1 - 2 * (Real.log y) ^ 2) + (-(3 / 10 : ℝ) * (y + 1) - 4 * Real.log y) := by
            ring
          _ ≤
              (y ^ 2 - 1 - 2 * (Real.log y) ^ 2) +
                (-2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
                  2 * Real.log (2 * Real.pi) * Real.log y) :=
            add_le_add (le_refl _) hboth
          _ = _ := by ring
      _ = _ := by ring
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 ≤
      (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 := by
    have hD := sub_le_sub_right hlogD (Real.log Real.pi)
    have hlogy2 : 0 ≤ 2 * Real.log y := mul_nonneg (by norm_num only) hlogy
    have hmul := mul_le_mul_of_nonneg_right hD hlogy2
    have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num only : (0 : ℝ) ≤ 1 / 2)
    have hsub := sub_le_sub_right hscaled (11 / 4)
    calc
      _ = 1 / 2 * ((Real.log ↑χ.conductor - Real.log Real.pi) * (2 * Real.log y)) - 11 / 4 := by
        ring
      _ ≤ 1 / 2 * ((y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y)) - 11 / 4 := hsub
      _ = _ := by ring
  constructor
  · exact hleft.trans hbase.1
  · apply hbase.2.trans
    calc
      _ =
          (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 +
            (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| :=
        by ring
      _ ≤
          (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 +
            (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| :=
        add_le_add_left hright _
      _ = _ := by ring

/-!
Input/assumptions: the zero branch at `X = y²`, with an even quadratic primitive character,
GRH, the weighted Riemann lower bound, and `log conductor ≤ y + log 4`.
Conclusion: the exact even main-error term is retained in the upper contour estimate.
Content: reuse the corrected lower bridge and specialize the exact whole-line generic API at `y²`.
Proof: transfer primitivity and nontriviality to the primitive character, then multiply the
conductor inequality by the nonnegative factor `log y`.
Role: supplies the refined c=0 interface for the B-bound and numerical comparison.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_log_four_even_exact {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                χ.primitiveCharacter| +
          (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcore := weightedComparisonCore_even_zero χ hne hquad heven hGRH hx64 hodd h2
  have hbounds := re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
    hriemann (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
    (lt_of_lt_of_le (by norm_num only) hx64) (le_trans (by norm_num only) hx64) hcore
  have hupper := hbounds.2.2.2
  rw [Real.log_div (by exact_mod_cast NeZero.ne χ.conductor) Real.pi_ne_zero] at hupper
  rw [hsqrt, hlogsq] at hupper
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) ≤
      (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) := by
    have hD := sub_le_sub_right hlogD (Real.log Real.pi)
    have hlogy2 : 0 ≤ 2 * Real.log y := mul_nonneg (by norm_num only) hlogy
    have hmul := mul_le_mul_of_nonneg_right hD hlogy2
    have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num only : (0 : ℝ) ≤ 1 / 2)
    calc
      _ = 1 / 2 * ((Real.log ↑χ.conductor - Real.log Real.pi) * (2 * Real.log y)) := by ring
      _ ≤ 1 / 2 * ((y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y)) := hscaled
      _ = _ := by ring
  constructor
  · exact (qNeOneAnalyticLowerBound_le_riemann_lower hy).trans hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ ≤ _ := by
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            add_le_add (le_refl _) (add_le_add hright (le_refl _))
          _ = _ := by ring

/-!
Input/assumptions: the even quadratic c=0 hypotheses, both Riemann lower bounds, `y ≥ 8`,
and `log conductor ≤ y + log 4` at `X = y²`.
Conclusion: the weighted character sum is bounded by the explicit B-free `log 4` envelope.
Content: multiply the reciprocal bound by the nonnegative contour coefficient and normalize the
conductor term; the exact `Ẽ₀` contribution is left untouched.
Role: pairs the common lower bound with
`PseudoPrime.LLS.Extensions.qNeOneAnalyticUpperBoundLogFour`.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_log_four_even_analytic_log_four
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneAnalyticUpperBoundLogFour y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_log_four_even_exact χ hne hquad heven
      hGRH hy hlogD hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_zero_branch_at_square_log_four χ hne hquad hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlogy)
  constructor
  · exact hbounds.1
  · have hmul := mul_le_mul_of_nonneg_left hB hcoef
    calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              (((1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 1 / 4 -
                  (2 * Real.log y - 8 / 5 - Real.log 2)) /
                (1 - 1 / y) ^ 2) +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by exact add_le_add (add_le_add hmul (le_refl _)) (le_refl _)
      _ = qNeOneAnalyticUpperBoundLogFour y := by
        unfold qNeOneAnalyticUpperBoundLogFour
        rw [Analysis.primitiveLogEvenMainError]

/-!
Input/assumptions: the c=-1 branch at `X = y²`, an even quadratic primitive character, GRH,
the weighted Riemann lower bound, and `log conductor ≤ y - log 4`.
Conclusion: the branch is connected to the exact whole-line upper while retaining its explicit
odd-tail square-log loss in the lower bound.
Content: specialize the c=-1 lower theorem and the exact generic even upper, then trade the
conductor term using `log y ≥ 0`.
Role: supplies the c=-1 branch comparison under `log conductor ≤ y - log 4`.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_log_four_even_exact {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y - Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
          2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
          (3 / 2) * (2 * Real.log y) ^ 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                χ.primitiveCharacter| +
          (1 / 2) * (y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hlower :=
    characterLogWeightedSum_re_ge_riemann_lower_sub_three_half_log_sq_of_eq_neg_one (y ^ 2) χ hquad
      hriemann (le_trans (by norm_num only) hx64) hodd h2
  rw [hsqrt, hlogsq] at hlower
  have hcore := weightedComparisonCore_even_neg_one χ hne hquad heven hGRH hx64 hodd h2
  have hbounds := re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
    hriemann (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
    (lt_of_lt_of_le (by norm_num only) hx64) (le_trans (by norm_num only) hx64) hcore
  have hupper := hbounds.2.2.2
  rw [Real.log_div (by exact_mod_cast NeZero.ne χ.conductor) Real.pi_ne_zero] at hupper
  rw [hsqrt, hlogsq] at hupper
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) ≤
      (1 / 2) * (y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y) := by
    have hD := sub_le_sub_right hlogD (Real.log Real.pi)
    have hlogy2 : 0 ≤ 2 * Real.log y := mul_nonneg (by norm_num only) hlogy
    have hmul := mul_le_mul_of_nonneg_right hD hlogy2
    have hscaled := mul_le_mul_of_nonneg_left hmul (by norm_num only : (0 : ℝ) ≤ 1 / 2)
    calc
      _ = 1 / 2 * ((Real.log ↑χ.conductor - Real.log Real.pi) * (2 * Real.log y)) := by ring
      _ ≤ 1 / 2 * ((y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y)) := hscaled
      _ = _ := by ring
  constructor
  · exact hlower
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ ≤ _ := by
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            add_le_add (le_refl _) (add_le_add hright (le_refl _))
          _ = _ := by ring

/-!
Input/assumptions: a quadratic primitive inducing character, the c=-1 branch at `X = y²`,
`y ≥ 8`, the Riemann weighted lower bound, and value `1` at the stated odd prime-power bases.
No conductor bound or GRH hypothesis is required beyond the supplied Riemann estimate.
Conclusion: `L₀ - δ ≤ Re S`; equivalently, the c=0 lower envelope bounds `Re S + δ`.
Content: the half-square correction and the alternating saving replace the former full
three-halves square-log loss.
Role: supplies the lower half of the corrected common comparison.
-/

theorem primitiveQuadraticLogWeightedLower_of_qneOne_neg_one_branch_corrected {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hquad : χ.primitiveCharacter.IsQuadratic)
    {y : ℝ} (hy : 8 ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBound y -
        Analysis.logTwoSquareCorrection y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
          χ.primitiveCharacter).re := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have h4 : (4 : ℝ) ≤ y ^ 2 := by
    have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 8 by norm_num only) hy
    calc
      (4 : ℝ) ≤ 64 := by norm_num only
      _ = 8 * 8 := by norm_num only
      _ ≤ y * y := hsq
      _ = y ^ 2 := by ring
  have hlower :=
    characterLogWeightedSum_re_ge_riemann_lower_half_log_sq_sub_delta_of_eq_neg_one (y ^ 2) χ hquad
      hriemann h4 hodd h2
  rw [hsqrt, hlogsq] at hlower
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 :=
    Analysis.log_two_mul_pi_lt.le.trans (by norm_num only)
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hmass : AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 20 : ℝ) :=
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
  unfold qNeOneAnalyticLowerBound
    Analysis.logTwoSquareCorrection
  have hAprod : 2 * Real.log (2 * Real.pi) * Real.log y ≤ 4 * Real.log y := by
    have hcoef : 2 * Real.log (2 * Real.pi) ≤ (4 : ℝ) := by
      calc
        2 * Real.log (2 * Real.pi) ≤ 2 * 2 := mul_le_mul_of_nonneg_left hlog2pi (by norm_num only)
        _ = 4 := by norm_num only
    exact mul_le_mul_of_nonneg_right hcoef hlogy
  have hmass2 : 2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ 2 * (3 / 20 : ℝ) :=
    mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 2 by norm_num only)
  have hy1 : (0 : ℝ) ≤ y + 1 := add_nonneg (le_trans (by norm_num only) hy) (by norm_num only)
  have hmassprod := mul_le_mul_of_nonneg_right hmass2 hy1
  have hAneg := neg_le_neg hAprod
  have hmassneg :
    -(3 / 10 : ℝ) * (y + 1) ≤
      -2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) := by
    calc
      -(3 / 10 : ℝ) * (y + 1) = -(2 * (3 / 20 : ℝ) * (y + 1)) := by ring
      _ ≤ -(2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1)) :=
        neg_le_neg hmassprod
      _ = _ := by ring
  have hcompare :
    y ^ 2 - 3 / 10 * (y + 1) - 4 * Real.log y - 1 - 2 * Real.log y ^ 2 -
        Real.log 2 * (2 * Real.log y - Real.log 2) ≤
      y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
        (2 * Real.log y) ^ 2 / 2 -
        Real.log 2 * (2 * Real.log y - Real.log 2) := by
    have hboth := add_le_add hmassneg hAneg
    calc
      _ =
          (y ^ 2 - 1 - 2 * (Real.log y) ^ 2 - Real.log 2 * (2 * Real.log y - Real.log 2)) +
            (-(3 / 10 : ℝ) * (y + 1) - 4 * Real.log y) :=
        by ring
      _ ≤
          (y ^ 2 - 1 - 2 * (Real.log y) ^ 2 - Real.log 2 * (2 * Real.log y - Real.log 2)) +
            (-2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
              2 * Real.log (2 * Real.pi) * Real.log y) :=
        add_le_add (le_refl _) hboth
      _ = _ := by ring
  exact hcompare.trans hlower

/-!
Input/assumptions: the c=-1 branch at `X = y²`, with `log conductor ≤ y`.
Conclusion: the branch is connected to the exact whole-line upper in the new radius.
Content: specialize the c=-1 lower theorem and trade the conductor term using `log y ≥ 0`.
Role: supplies the exact upper and coarse c=-1 lower bounds before correction comparison.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_even_exact_le {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBoundNegOne y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                χ.primitiveCharacter| +
          (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hlower :=
    characterLogWeightedSum_re_ge_riemann_lower_sub_three_half_log_sq_of_eq_neg_one (y ^ 2) χ hquad
      hriemann (le_trans (by norm_num only) hx64) hodd h2
  rw [hsqrt, hlogsq] at hlower
  have hcore := weightedComparisonCore_even_neg_one χ hne hquad heven hGRH hx64 hodd h2
  have hbounds := re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
    hriemann (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
    (lt_of_lt_of_le (by norm_num only) hx64) (le_trans (by norm_num only) hx64) hcore
  have hupper := hbounds.2.2.2
  rw [Real.log_div (by exact_mod_cast NeZero.ne χ.conductor) Real.pi_ne_zero] at hupper
  rw [hsqrt, hlogsq] at hupper
  have hmass : AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 20 : ℝ) :=
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans hy)
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 :=
    Analysis.log_two_mul_pi_lt.le.trans (by norm_num only)
  have hleft :
    qNeOneAnalyticLowerBoundNegOne y ≤
      y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
        (3 / 2) * (2 * Real.log y) ^ 2 := by
    unfold qNeOneAnalyticLowerBoundNegOne
    exact le_rfl
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) ≤
      (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) := by
    have hleft :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi))
        (by norm_num only : (0 : ℝ) ≤ 1 / 2)
    have hright :=
      mul_le_mul_of_nonneg_right hleft (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hlogy)
    exact hright.trans_eq (by ring)
  constructor
  · exact hleft.trans hlower
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ ≤ _ := by
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            add_le_add (le_refl _) (add_le_add hright (le_refl _))
          _ = _ := by ring

/-!
Input/assumptions: the even quadratic c=-1 hypotheses, both Riemann lower bounds, `y ≥ 8`,
and `log conductor ≤ y`.
Conclusion: the c=-1 weighted sum is bounded by the B-free `log conductor ≤ y` envelope.
Content: multiply the adapter by the nonnegative contour coefficient and retain the common
even main-error term.
Role: supplies the upper bound before adding the logarithmic correction loss.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_even_analytic_le {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBoundNegOne y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneAnalyticUpperBoundNegOne y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_even_exact_le χ hne hquad heven
      hGRH hy hlogD hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_neg_one_branch_at_square_le χ hne hquad heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans hy)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlogy)
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              (((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
                  (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
                (1 - 1 / y) ^ 2) +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by exact add_le_add (add_le_add hmul (le_refl _)) (le_refl _)
      _ = qNeOneAnalyticUpperBoundNegOne y := by
        unfold qNeOneAnalyticUpperBoundNegOne
        rw [Analysis.primitiveLogEvenMainError]

/-! The c=0 comparison upper envelope with the common exact even main-error term. -/

noncomputable def qNeOneUpperBoundZeroStar (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundZeroStar y +
    (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
    Analysis.primitiveLogEvenMainError (y ^ 2)

/-! The rationalized `B₀*` bound is lifted to the exact c=0 upper envelope. -/

theorem qNeOneUpperBoundZeroStar_le_rationalized {y : ℝ} (hy : 12 ≤ y) :
    qNeOneUpperBoundZeroStar y ≤
      (2 * y + 2 + 2 * Real.log y) *
          (((1 / 2) * (1 - 1 / y ^ 2) * (y + 39 / 100) - 4 / 5 -
              (2 * Real.log y - 8 / 5 - Real.log 2)) /
            (1 - 1 / y) ^ 2) +
        (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
        Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    have hlog : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlog)
  have hB := qNeOneBUpperBoundZeroStar_le_rationalized hy
  unfold qNeOneUpperBoundZeroStar
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  exact add_le_add (add_le_add hmul (le_refl _)) (le_refl _)

/-!
Input/assumptions: a radius `y ≥ 12`.
Conclusion: the exact c=0 upper envelope can consume the linear B bound.
Content: only the positive coefficient of `B₀*` is relaxed; the even main-error term remains exact.
Role: a coarse relaxation of the zero-branch envelope using `B₀* ≤ y + 3`.
-/

theorem qNeOneUpperBoundZeroStar_le_linear {y : ℝ} (hy : 12 ≤ y) :
    qNeOneUpperBoundZeroStar y ≤
      (2 * y + 2 + 2 * Real.log y) * (y + 3) +
        (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
        Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    have hlog : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlog)
  have hB := qNeOneBUpperBoundZeroStar_le_linear hy
  unfold qNeOneUpperBoundZeroStar
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  exact add_le_add (add_le_add hmul (le_refl _)) (le_refl _)

/-! The c=-1 comparison upper envelope with the common exact even main-error term. -/

noncomputable def qNeOneUpperBoundNegOneStar (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundNegOneStar y +
    (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
    Analysis.primitiveLogEvenMainError (y ^ 2)

/-! A common upper envelope for the zero, one, and corrected negative-one branches. -/

noncomputable def qNeOneCommonUpperBound (y : ℝ) : ℝ :=
  max (qNeOneUpperBoundZeroStar y) (qNeOneAnalyticUpperBoundOne y)

/-!
Input/assumptions: an affine B-bound at radius `y ≥ 12` and a separate
strict inequality for the resulting relaxed whole-line upper bound.
Conclusion: the exact c=0 upper envelope lies strictly below the common lower
envelope.
Content: lift the B-bound through the nonnegative coefficient, use the exact
even main-error relaxation, and consume the supplied separation polynomial.
Role: common comparison used by the compact-interval separation certificates.
-/

theorem qNeOneUpperBoundZeroStar_lt_of_affine_B {y C : ℝ} (hy : 12 ≤ y)
    (hB : qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + C)
    (hsep :
      (2 * y + 2 + 2 * Real.log y) * (y / 2 - 2 * Real.log y + C) + (y + 2 / 5) * Real.log y +
            2 / 3 -
          (1 / 2) * Real.log y -
          2 * (Real.log y) ^ 2 <
        qNeOneAnalyticLowerBound y) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hA : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlogy)
  have hprod := mul_le_mul_of_nonneg_left hB hA
  have hcondupper :
    (y + Real.log 4 - Real.log Real.pi) * Real.log y ≤ (y + 2 / 5) * Real.log y := by
    have hlog4 : Real.log (4 : ℝ) ≤ (139 / 100 : ℝ) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only
      have h := mul_le_mul_of_nonneg_left (Real.log_two_lt_d9.le) (by norm_num only : (0 : ℝ) ≤ 2)
      norm_num only at h ⊢
      exact h.trans (by norm_num only)
    have hlogpi : 1 ≤ Real.log Real.pi := by
      have h3pi :=
        Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
          (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
      exact (le_trans (by norm_num only) Real.log_three_gt_d9.le).trans h3pi
    have hcond : y + Real.log 4 - Real.log Real.pi ≤ y + 2 / 5 := by
      have hlin : Real.log 4 - Real.log Real.pi ≤ (2 / 5 : ℝ) := by
        exact (sub_le_sub hlog4 hlogpi).trans (by norm_num only)
      calc
        y + Real.log 4 - Real.log Real.pi = (Real.log 4 - Real.log Real.pi) + y := by ring
        _ ≤ 2 / 5 + y := add_le_add hlin (le_refl y)
        _ = y + 2 / 5 := by ring
    have h2 := mul_le_mul_of_nonneg_right hcond hlogy
    exact h2
  have heuler : (1 / 2 : ℝ) ≤ Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant.le
  have hpi : Real.pi ^ 2 / 24 ≤ (2 / 3 : ℝ) := by
    have hprodpi : 0 < (4 - Real.pi) * (4 + Real.pi) :=
      mul_pos (by linarith [Real.pi_lt_d4]) (by positivity)
    have hsq : Real.pi ^ 2 < 16 := by
      rw [show (4 - Real.pi) * (4 + Real.pi) = 16 - Real.pi ^ 2 by ring] at hprodpi
      linarith
    have hsqdiv : Real.pi ^ 2 / 24 < (16 : ℝ) / 24 := div_lt_div_of_pos_right hsq (by norm_num only)
    exact hsqdiv.le.trans_eq (by norm_num only)
  have hE :
    Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log (y ^ 2) -
        (1 / 2) * Real.log (y ^ 2) ^ 2 ≤
      2 / 3 - (1 / 2) * Real.log y - 2 * (Real.log y) ^ 2 := by
    have hlogpow : Real.log (y ^ 2) = 2 * Real.log y := by
      rw [Real.log_pow]
      norm_num only
    rw [hlogpow]
    have heuler0 : 0 ≤ Real.eulerMascheroniConstant := by linarith
    calc
      Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * (2 * Real.log y) -
            (1 / 2) * (2 * Real.log y) ^ 2 ≤
          (2 / 3 : ℝ) - (Real.eulerMascheroniConstant / 2) * (2 * Real.log y) -
            (1 / 2) * (2 * Real.log y) ^ 2 :=
        by
        convert
            sub_le_sub_right hpi
              ((Real.eulerMascheroniConstant / 2) * (2 * Real.log y) +
                (1 / 2) * (2 * Real.log y) ^ 2) using
            1 <;>
          ring
      _ ≤ 2 / 3 - (1 / 2) * Real.log y - 2 * (Real.log y) ^ 2 := by
        rw [show (1 / 2 : ℝ) * (2 * Real.log y) ^ 2 = 2 * (Real.log y) ^ 2 by ring]
        have hterm :
          (1 / 2 : ℝ) * Real.log y ≤ (Real.eulerMascheroniConstant / 2) * (2 * Real.log y) := by
          rw [show
              (Real.eulerMascheroniConstant / 2) * (2 * Real.log y) =
                Real.eulerMascheroniConstant * Real.log y
              by ring]
          exact mul_le_mul_of_nonneg_right heuler hlogy
        have hmain :
          (2 / 3 : ℝ) - 2 * (Real.log y) ^ 2 -
              (Real.eulerMascheroniConstant / 2) * (2 * Real.log y) ≤
            (2 / 3 : ℝ) - 2 * (Real.log y) ^ 2 - (1 / 2) * Real.log y := by
          exact sub_le_sub_left hterm _
        convert hmain using 1 <;> ring
  have hU :
    qNeOneUpperBoundZeroStar y ≤
      (2 * y + 2 + 2 * Real.log y) * (y / 2 - 2 * Real.log y + C) + (y + 2 / 5) * Real.log y +
          2 / 3 -
        (1 / 2) * Real.log y -
        2 * (Real.log y) ^ 2 := by
    unfold qNeOneUpperBoundZeroStar
    rw [Analysis.primitiveLogEvenMainError]
    rw [show Real.log (y ^ 2) = 2 * Real.log y by
        rw [Real.log_pow]; norm_num only]
    have hcondscaled :
      (1 / 2 : ℝ) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) ≤
        (y + 2 / 5) * Real.log y := by
      calc
        (1 / 2 : ℝ) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) =
            (y + Real.log 4 - Real.log Real.pi) * Real.log y :=
          by ring
        _ ≤ (y + 2 / 5) * Real.log y := hcondupper
    have hE' := hE
    rw [show Real.log (y ^ 2) = 2 * Real.log y by
        rw [Real.log_pow]; norm_num only] at hE'
    have hsum := add_le_add (add_le_add hprod hcondscaled) hE'
    simpa only [add_sub_assoc] using hsum
  exact hU.trans_lt hsep

/-!
Input/assumptions: `12 ≤ y ≤ 13`.
Conclusion: the c=0 whole-line upper is strictly below the lower envelope.
Role: the separation certificate on `[12,13]`.
-/

theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_twelve_thirteen {y : ℝ} (hy : 12 ≤ y)
    (hy13 : y ≤ 13) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hloglower : (247 : ℝ) / 100 + 2 / 25 * (y - 12) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (12 : ℝ)) (b := 13) (y := y) (L :=
        247 / 100) (by norm_num only) (by norm_num only) hy hy13 Analysis.log_twelve_gt
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_twelve_thirteen hy hy13
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B hy hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (by linarith : (0 : ℝ) ≤ y)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith [hyl, hL2, sq_nonneg (y - 12), sq_nonneg (y - 13)]

/-! The remaining compact intervals use the same cleared separation inequality. -/

theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_thirteen_sixteen {y : ℝ} (hy : 13 ≤ y)
    (hy16 : y ≤ 16) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hlog13 : (256 : ℝ) / 100 < Real.log 13 := by
    have h12 : (248 : ℝ) / 100 < Real.log 12 := by
      rw [show (12 : ℝ) = 3 * 4 by norm_num only,
        Real.log_mul (by norm_num only) (by norm_num only), Real.log_four_eq]
      have h2 : (693 : ℝ) / 1000 < Real.log 2 := lt_trans (by norm_num only) Real.log_two_gt_d9
      have h3 : (1095 : ℝ) / 1000 < Real.log 3 := lt_trans (by norm_num only) Real.log_three_gt_d9
      calc
        (248 : ℝ) / 100 < 2481 / 1000 := by norm_num only
        _ = 1095 / 1000 + 2 * (693 / 1000) := by norm_num only
        _ < Real.log 3 + 2 * Real.log 2 := by
          exact add_lt_add h3 (mul_lt_mul_of_pos_left h2 (by norm_num only))
    have hfac : (12 : ℝ) * (13 / 12) = 13 := by norm_num only
    rw [← hfac, Real.log_mul (by norm_num only) (by norm_num only)]
    have hla := Real.le_log_one_add_of_nonneg (x := (1 / 12 : ℝ)) (by norm_num only)
    norm_num only at hla
    have hsum := add_lt_add_of_lt_of_le h12 hla
    calc
      (256 : ℝ) / 100 = 248 / 100 + 2 / 25 := by norm_num only
      _ < Real.log 12 + Real.log (13 / 12) := hsum
  have hloglower : (256 : ℝ) / 100 + 2 / 29 * (y - 13) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (13 : ℝ)) (b := 16) (y := y) (L :=
        256 / 100) (by norm_num only) (by norm_num only) hy hy16 hlog13
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_thirteen_sixteen hy hy16
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith [hyl, hL2, sq_nonneg (y - 13), sq_nonneg (y - 16)]

theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_sixteen_twenty_four {y : ℝ}
    (hy : 16 ≤ y) (hy24 : y ≤ 24) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hlog16 : (277 : ℝ) / 100 < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    have h2 : (693 : ℝ) / 1000 < Real.log 2 := lt_trans (by norm_num only) Real.log_two_gt_d9
    calc
      (277 : ℝ) / 100 < 2772 / 1000 := by norm_num only
      _ = 4 * (693 / 1000) := by norm_num only
      _ < 4 * Real.log 2 := mul_lt_mul_of_pos_left h2 (by norm_num only)
  have hloglower : (277 : ℝ) / 100 + 1 / 20 * (y - 16) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (16 : ℝ)) (b := 24) (y := y) (L :=
        277 / 100) (by norm_num only) (by norm_num only) hy hy24 hlog16
    norm_num only at h ⊢
    exact h.le
  have hB :=
    qNeOneBUpperBoundZeroStar_le_affine_sixteen_twenty_four hy hy24
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith [hyl, hL2, sq_nonneg (y - 16), sq_nonneg (y - 24)]

theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_twenty_four_thirty_two {y : ℝ}
    (hy : 24 ≤ y) (hy32 : y ≤ 32) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hlog24 : (317 : ℝ) / 100 < Real.log 24 := by
    rw [show (24 : ℝ) = 3 * 2 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    have h2 : (693 : ℝ) / 1000 < Real.log 2 := lt_trans (by norm_num only) Real.log_two_gt_d9
    have h3 : (1095 : ℝ) / 1000 < Real.log 3 := lt_trans (by norm_num only) Real.log_three_gt_d9
    calc
      (317 : ℝ) / 100 < 3174 / 1000 := by norm_num only
      _ = 1095 / 1000 + 3 * (693 / 1000) := by norm_num only
      _ < Real.log 3 + 3 * Real.log 2 := by
        exact add_lt_add h3 (mul_lt_mul_of_pos_left h2 (by norm_num only))
  have hloglower : (317 : ℝ) / 100 + 1 / 28 * (y - 24) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (24 : ℝ)) (b := 32) (y := y) (L :=
        317 / 100) (by norm_num only) (by norm_num only) hy hy32 hlog24
    norm_num only at h ⊢
    exact h.le
  have hB :=
    qNeOneBUpperBoundZeroStar_le_affine_twenty_four_thirty_two hy hy32
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith [hyl, hL2, sq_nonneg (y - 24), sq_nonneg (y - 32)]

theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_thirty_two_forty_eight {y : ℝ}
    (hy : 32 ≤ y) (hy48 : y ≤ 48) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hlog32 : (346 : ℝ) / 100 < Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    have h2 : (693 : ℝ) / 1000 < Real.log 2 := lt_trans (by norm_num only) Real.log_two_gt_d9
    calc
      (346 : ℝ) / 100 < 3465 / 1000 := by norm_num only
      _ = 5 * (693 / 1000) := by norm_num only
      _ < 5 * Real.log 2 := mul_lt_mul_of_pos_left h2 (by norm_num only)
  have hloglower : (346 : ℝ) / 100 + 1 / 40 * (y - 32) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (32 : ℝ)) (b := 48) (y := y) (L :=
        346 / 100) (by norm_num only) (by norm_num only) hy hy48 hlog32
    norm_num only at h ⊢
    exact h.le
  have hB :=
    qNeOneBUpperBoundZeroStar_le_affine_thirty_two_forty_eight hy hy48
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num only) hy
  have hbase3 : (3 : ℝ) ≤ 346 / 100 + 1 / 40 * (y - 32) := by
    have hterm : (0 : ℝ) ≤ 1 / 40 * (y - 32) := mul_nonneg (by norm_num only) (sub_nonneg.mpr hy)
    calc
      (3 : ℝ) ≤ 346 / 100 := by norm_num only
      _ ≤ 346 / 100 + 1 / 40 * (y - 32) := le_add_of_nonneg_right hterm
  have hL3 : (3 : ℝ) ≤ Real.log y := hbase3.trans hloglower
  have hyl3 := mul_le_mul_of_nonneg_left hL3 hy0
  have hL23 := mul_le_mul_of_nonneg_right hL3 hLpos
  have hprod1 : 1800 * y ≤ 600 * y * Real.log y := by
    calc
      1800 * y = 600 * (3 * y) := by ring
      _ ≤ 600 * (y * Real.log y) := by
        exact
          mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using hyl3)
            (show (0 : ℝ) ≤ 600 by norm_num only)
      _ = 600 * y * Real.log y := by ring
  have hprod2 : 3600 * Real.log y ≤ 1200 * (Real.log y) ^ 2 := by
    calc
      3600 * Real.log y = 1200 * (3 * Real.log y) := by ring
      _ ≤ 1200 * (Real.log y * Real.log y) :=
        mul_le_mul_of_nonneg_left hL23 (show (0 : ℝ) ≤ 1200 by norm_num only)
      _ = 1200 * (Real.log y) ^ 2 := by ring
  have hgap : 2030 + 30 * y < 2190 * Real.log y := by
    have hsmall : 2030 + 30 * y ≤ (3470 : ℝ) := by
      calc
        2030 + 30 * y ≤ 2030 + 30 * 48 :=
          add_le_add_right (mul_le_mul_of_nonneg_left hy48 (show (0 : ℝ) ≤ 30 by norm_num only)) _
        _ = 3470 := by norm_num only
    have hlarge : (3470 : ℝ) < 2190 * 3 := by norm_num only
    have hscale : 2190 * 3 ≤ 2190 * Real.log y :=
      mul_le_mul_of_nonneg_left hL3 (show (0 : ℝ) ≤ 2190 by norm_num only)
    exact hsmall.trans_lt (hlarge.trans_le hscale)
  have hlin : 2030 + 1830 * y + 1410 * Real.log y < 1800 * y + 3600 * Real.log y := by
    calc
      2030 + 1830 * y + 1410 * Real.log y = (2030 + 30 * y) + (1800 * y + 1410 * Real.log y) := by
        ring
      _ < 2190 * Real.log y + (1800 * y + 1410 * Real.log y) := by
        have hadd := add_lt_add_right hgap (1800 * y + 1410 * Real.log y)
        convert hadd using 1 <;> ring
      _ = 1800 * y + 3600 * Real.log y := by ring
  have hmain :
    2030 + 1830 * y + 1410 * Real.log y < 600 * y * Real.log y + 1200 * (Real.log y) ^ 2 := by
    calc
      2030 + 1830 * y + 1410 * Real.log y < 1800 * y + 3600 * Real.log y := hlin
      _ ≤ 600 * y * Real.log y + 1200 * (Real.log y) ^ 2 := by
        have hsum := add_le_add hprod1 hprod2
        calc
          1800 * y + 3600 * Real.log y = (1800 * y) + (3600 * Real.log y) := by ring
          _ ≤ (600 * y * Real.log y) + (1200 * (Real.log y) ^ 2) := hsum
  have hdiff :
    0 <
      (-390 - y * 90 + y ^ 2 * 300 - Real.log y * 1200 - Real.log y ^ 2 * 600) -
        (1640 + y * 1740 - y * Real.log y * 600 + y ^ 2 * 300 + Real.log y * 210 -
          Real.log y ^ 2 * 1800) := by
    calc
      0 <
          (600 * y * Real.log y + 1200 * (Real.log y) ^ 2) -
            (2030 + 1830 * y + 1410 * Real.log y) :=
        sub_pos.mpr hmain
      _ = _ := by ring
  have hdiff' :
    0 <
      ((-390 - y * 90 + y ^ 2 * 300 - Real.log y * 1200 - Real.log y ^ 2 * 600) -
          (1640 + y * 1740 - y * Real.log y * 600 + y ^ 2 * 300 + Real.log y * 210 -
            Real.log y ^ 2 * 1800)) /
        (300 : ℝ) :=
    div_pos hdiff (by norm_num only)
  have hdiff'' :
    0 <
      (-13 / 10 + y * (-3 / 10) + y ^ 2 - Real.log y * 4 - Real.log y ^ 2 * 2) -
        (82 / 15 + y * (29 / 5) - y * Real.log y * 2 + y ^ 2 + Real.log y * (7 / 10) -
          Real.log y ^ 2 * 6) := by
    calc
      0 <
          ((-390 - y * 90 + y ^ 2 * 300 - Real.log y * 1200 - Real.log y ^ 2 * 600) -
              (1640 + y * 1740 - y * Real.log y * 600 + y ^ 2 * 300 + Real.log y * 210 -
                Real.log y ^ 2 * 1800)) /
            (300 : ℝ) :=
        hdiff'
      _ = _ := by ring
  exact sub_pos.mp hdiff''

/-! The five compact c=0 certificates combine with the c=1 bound on `[12,48]`. -/

theorem qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_twelve_forty_eight {y : ℝ} (hy : 12 ≤ y)
    (hy48 : y ≤ 48) :
    qNeOneCommonUpperBound y < qNeOneAnalyticLowerBound y := by
  have hone :=
    qNeOneAnalyticUpperBoundOne_lt_qNeOneAnalyticLowerBound (y := y)
      (by exact (le_trans (by norm_num only) hy))
  have hzero :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
    by_cases hy13 : y ≤ 13
    · exact qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_twelve_thirteen hy hy13
    by_cases hy16 : y ≤ 16
    · exact
        qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_thirteen_sixteen (le_of_not_ge hy13)
          hy16
    by_cases hy24 : y ≤ 24
    · exact
        qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_sixteen_twenty_four (le_of_not_ge hy16)
          hy24
    by_cases hy32 : y ≤ 32
    · exact
        qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_twenty_four_thirty_two
          (le_of_not_ge hy24) hy32
    · exact
        qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_thirty_two_forty_eight
          (le_of_not_ge hy32) hy48
  unfold qNeOneCommonUpperBound
  exact max_lt hzero hone

namespace QNeOneZeroStar


/-- The affine comparison is below the analytic envelope by the positive gap certificate. -/
lemma zeroStar_affine_lt_lower {y : ℝ} (hy : 48 ≤ y) :
    (2 * y + 2 + 2 * Real.log y) * (y / 2 - 2 * Real.log y + 3) + (y + 2 / 5) * Real.log y + 2 / 3 -
        (1 / 2) * Real.log y -
        2 * (Real.log y) ^ 2 <
      qNeOneAnalyticLowerBound y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hcert :=
    Analysis.affine_log_gap_pos hypos.le
      (Analysis.zeroStar_log_lower hy hypos)
  apply sub_pos.mp
  exact
    (div_pos hcert (by norm_num only : (0 : ℝ) < 300)).trans_eq
      (by
        unfold qNeOneAnalyticLowerBound; ring)

end QNeOneZeroStar

/-- For `48 ≤ y`, the zero-branch upper bound is below the analytic lower envelope.
The numerator and affine separation follow from explicit nonnegative polynomial certificates.
This supplies the zero branch of the common-upper-bound separation. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound {y : ℝ} (hy : 48 ≤ y) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  exact
    qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy)
      (Analysis.reciprocal_log_quotient_le_affine hy)
      (QNeOneZeroStar.zeroStar_affine_lt_lower hy)

/-! The two branch separations combine into the max upper envelope without differentiating it. -/

theorem qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound {y : ℝ} (hy : 48 ≤ y) :
    qNeOneCommonUpperBound y < qNeOneAnalyticLowerBound y := by
  have hzero := qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound hy
  have hone :=
    qNeOneAnalyticUpperBoundOne_lt_qNeOneAnalyticLowerBound (y := y)
      (by linarith)
  unfold qNeOneCommonUpperBound
  exact max_lt hzero hone

/-! The compact certificates and the old tail certificate give separation on `y ≥ 12`. -/

theorem qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_of_twelve {y : ℝ} (hy : 12 ≤ y) :
    qNeOneCommonUpperBound y < qNeOneAnalyticLowerBound y := by
  by_cases hy48 : y ≤ 48
  · exact qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_twelve_forty_eight hy hy48
  · exact qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound (by linarith)

/-! Any sandwich by the common numerical upper envelope is impossible in the bound range. -/

theorem qNeOne_common_sandwich_false {y z : ℝ} (hy : 48 ≤ y)
    (hlower : qNeOneAnalyticLowerBound y ≤ z)
    (hupper : z ≤ qNeOneCommonUpperBound y) : False := by
  exact
    (not_lt_of_ge (hlower.trans hupper))
      (qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound (by linarith))

/-! The same common sandwich contradiction is now available from `y ≥ 12`. -/

theorem qNeOne_common_sandwich_false_of_twelve {y z : ℝ} (hy : 12 ≤ y)
    (hlower : qNeOneAnalyticLowerBound y ≤ z)
    (hupper : z ≤ qNeOneCommonUpperBound y) : False := by
  exact
    (not_lt_of_ge (hlower.trans hupper))
      (qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_of_twelve hy)

/-!
Input/assumptions: the c=0 even quadratic branch with `log conductor ≤ y + log 4`.
Conclusion: the strong `B₀*` bound gives the exact common-error upper `U₀*`.
Content: retain the `-4/5` reciprocal remainder and the exact even main-error term.
Role: supplies the c=0 upper used in the corrected c=-1 comparison.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_star {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneUpperBoundZeroStar y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_log_four_even_exact χ hne hquad heven
      hGRH hy hlogD hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_zero_branch_even_at_square_log_four_strong χ hne hquad heven
      hGRH hy hlogD hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundZeroStar y +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by
        rw [qNeOneBUpperBoundZeroStar]
        linarith
      _ = qNeOneUpperBoundZeroStar y := by rfl

/-! The c=0 exact/B-free bounds lift to the three-branch common upper envelope. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneCommonUpperBound y := by
  have h :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_star χ hne hquad heven hGRH hy
      hlogD hriemann hriemannReciprocal hodd h2
  constructor
  · exact h.1
  · exact
      h.2.trans
        (show qNeOneUpperBoundZeroStar y ≤ qNeOneCommonUpperBound y
          by
          unfold qNeOneCommonUpperBound
          exact le_max_left _ _)

/-!
Input/assumptions: the c=-1 even quadratic branch with `log conductor ≤ y`.
Conclusion: the exact c=-1 upper is the B-free envelope `U₋*`.
Role: supplies the upper half of the corrected comparison.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_even_star {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBoundNegOne y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneUpperBoundNegOneStar y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_even_exact_le χ hne hquad heven
      hGRH hy hlogD hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_neg_one_branch_at_square_le χ hne hquad heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundNegOneStar y +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by
        rw [qNeOneBUpperBoundNegOneStar]
        linarith
      _ = qNeOneUpperBoundNegOneStar y := by rfl

/-!
The gap between the c=0 upper and the corrected c=-1 upper has the explicit expression below.
The common exact even main-error term cancels from the equality.
-/

theorem qNeOneUpperBoundZeroStar_sub_negOneStar_add_delta_eq {y : ℝ} (hy : 8 ≤ y) :
    qNeOneUpperBoundZeroStar y -
        (qNeOneUpperBoundNegOneStar y + Analysis.logTwoSquareCorrection y) =
      (2 * y + 2 + 2 * Real.log y) * (Real.log 2 * (2 / 3 - 1 / y ^ 2) / (1 - 1 / y) ^ 2) +
        (Real.log 2) ^ 2 := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
  have hden : (1 - 1 / y) ^ 2 ≠ 0 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  have hB := qNeOneBUpperBoundZeroStar_sub_negOneStar_eq hy
  rw [qNeOneUpperBoundZeroStar, qNeOneUpperBoundNegOneStar,
    Analysis.logTwoSquareCorrection, hlog4]
  calc
    _ =
        (2 * y + 2 + 2 * Real.log y) *
            (qNeOneBUpperBoundZeroStar y -
              qNeOneBUpperBoundNegOneStar y) +
          (Real.log 2) ^ 2 :=
      by ring_nf
    _ = _ := by rw [hB]

/-!
The corrected c=-1 branch is now sandwiched by the c=0 comparison upper:
`L₀ ≤ Re S₋ + δ ≤ U₀*`. This comparison keeps the exact even error term.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_corrected_star {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
              χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
              χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ≤
        qNeOneUpperBoundZeroStar y := by
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hcore := weightedComparisonCore_even_neg_one χ hne hquad heven hGRH hx hodd h2
  have hc := re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
    hriemann hriemannReciprocal (lt_of_lt_of_le (by norm_num only) hx)
    (le_trans (by norm_num only) hx) hcore
  have hlow : qNeOneAnalyticLowerBound y - Analysis.logTwoSquareCorrection y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
        χ.primitiveCharacter).re := by
    have hl := qNeOneAnalyticLowerBound_le_riemann_lower hy
    have hs := hc.1
    rw [Analysis.logTwoSquareCorrection]
    rw [Real.log_pow] at hl hs
    norm_num only at hl hs
    linarith only [hl, hs]
  have hupp :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_even_star χ hne hquad heven hGRH hy
      hlogD hriemann hriemannReciprocal hodd h2
  have hdiff := qNeOneUpperBoundZeroStar_sub_negOneStar_add_delta_eq hy
  constructor
  · linarith
  · have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
    have hsqpos : 0 < y ^ 2 := sq_pos_of_pos hypos
    have hfactor : 0 ≤ 2 / 3 - 1 / y ^ 2 := by
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hsqpos).2
      have hy2 : (64 : ℝ) ≤ y ^ 2 := by
        have h := mul_le_mul hy hy (by norm_num only : (0 : ℝ) ≤ 8) (by linarith : (0 : ℝ) ≤ y)
        norm_num only at h
        simpa only [pow_two] using h
      calc
        (1 : ℝ) ≤ (2 / 3 : ℝ) * 64 := by norm_num only
        _ ≤ (2 / 3 : ℝ) * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (by norm_num only)
    have hdenpos : 0 < (1 - 1 / y) ^ 2 :=
      sq_pos_of_pos (sub_pos.mpr ((div_lt_one hypos).2 (by linarith)))
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num only)
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith
    have hgap :
      0 ≤
        (2 * y + 2 + 2 * Real.log y) * (Real.log 2 * (2 / 3 - 1 / y ^ 2) / (1 - 1 / y) ^ 2) +
          (Real.log 2) ^ 2 := by
      exact
        add_nonneg (mul_nonneg hcoef (div_nonneg (mul_nonneg hlog2pos.le hfactor) hdenpos.le))
          (sq_nonneg _)
    have hnonneg :
      0 ≤
        qNeOneUpperBoundZeroStar y -
          (qNeOneUpperBoundNegOneStar y + Analysis.logTwoSquareCorrection y) := by
      rw [hdiff]
      exact hgap
    have hupper :
      qNeOneUpperBoundNegOneStar y + Analysis.logTwoSquareCorrection y ≤
        qNeOneUpperBoundZeroStar y :=
      sub_nonneg.mp hnonneg
    exact (add_le_add hupp.2 (le_refl _)).trans hupper

/-! The corrected c=-1 bounds also lift to the common upper envelope. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_corrected_common {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
              χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
              χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ≤
        qNeOneCommonUpperBound y := by
  have h :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_corrected_star χ hne hquad heven
      hGRH hy hlogD hriemann hriemannReciprocal hodd h2
  constructor
  · exact h.1
  · exact
      h.2.trans
        (show qNeOneUpperBoundZeroStar y ≤ qNeOneCommonUpperBound y
          by
          unfold qNeOneCommonUpperBound
          exact le_max_left _ _)

/-!
Input/assumptions: the c=-1 exact bridge and the square-radius reciprocal B adapter.
Conclusion: the c=-1 weighted sum is bounded by the explicit B-free `log 4` envelope.
Content: multiply the adapter by the nonnegative contour coefficient and preserve the exact
even main-error term.
Role: supplies the c=-1 B-free L/U interface for the subsequent branch comparison.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_log_four_even_analytic {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y - Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBoundNegOne y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneAnalyticUpperBoundNegOneLogFour y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_log_four_even_exact χ hne hquad
      heven hGRH hy hlogD hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_neg_one_branch_at_square χ hne hquad heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              (((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log 4 - Real.log Real.pi) - 4 / 5 -
                  (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
                (1 - 1 / y) ^ 2) +
            (1 / 2) * (y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by linarith
      _ = qNeOneAnalyticUpperBoundNegOneLogFour y := by
        unfold qNeOneAnalyticUpperBoundNegOneLogFour
        rw [Analysis.primitiveLogEvenMainError]

/-!
Input/assumptions: the c=1 branch at `X = y²`, an even quadratic primitive character, GRH,
the weighted Riemann lower bound, and `log conductor ≤ y`.
Conclusion: the c=1 branch is connected to the exact whole-line upper with the analytic lower
bound and the retained even main-error term.
Content: normalize the existing c=1 lower estimate and specialize the exact generic upper.
Role: supplies the exact c=1 interface before the reciprocal B substitution.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_exact {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                χ.primitiveCharacter| +
          (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcore := weightedComparisonCore_even_one χ hne hquad heven hGRH hx64 hodd h2
  have hbounds := re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
    hriemann (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
    (lt_of_lt_of_le (by norm_num only) hx64) (le_trans (by norm_num only) hx64) hcore
  have hupper := hbounds.2.2.2
  rw [Real.log_div (by exact_mod_cast NeZero.ne χ.conductor) Real.pi_ne_zero] at hupper
  rw [hsqrt, hlogsq] at hupper
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans hy)
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) ≤
      (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) := by
    have hleft :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi))
        (by norm_num only : (0 : ℝ) ≤ 1 / 2)
    have hright :=
      mul_le_mul_of_nonneg_right hleft (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hlogy)
    exact hright.trans_eq (by ring)
  constructor
  · exact (qNeOneAnalyticLowerBound_le_riemann_lower hy).trans hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ =
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
              Analysis.primitiveLogEvenMainError (y ^ 2)) :=
        by ring
      _ ≤ _ := add_le_add (le_refl _) (add_le_add hright (le_refl _))
      _ = _ := by ring

/-!
Input/assumptions: the exact c=1 bridge and the square-radius reciprocal B bound.
Conclusion: the weighted character sum is bounded by the explicit c=1 B-free envelope.
Content: multiply the reciprocal bound by the nonnegative contour coefficient and preserve the
exact even main-error term.
Role: supplies the c=1 analytic L/U interface for the branch comparison.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneAnalyticUpperBoundOne y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_exact χ hne hquad heven hGRH hy
      hlogD hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_one_branch_at_square_simple χ hne hquad heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by linarith
      _ = qNeOneAnalyticUpperBoundOne y := by
        unfold qNeOneAnalyticUpperBoundOne
        rw [Analysis.primitiveLogEvenMainError]

/-! The c=1 branch lifts to the same explicit common upper envelope. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneCommonUpperBound y := by
  have h :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_analytic χ hne hquad heven hGRH hy
      hlogD hriemann hriemannReciprocal hodd h2
  constructor
  · exact h.1
  · exact
      h.2.trans
        (show qNeOneAnalyticUpperBoundOne y ≤ qNeOneCommonUpperBound y
          by
          unfold qNeOneCommonUpperBound
          exact le_max_right _ _)

/-! The three common branch bounds contradict numerical separation for `y ≥ 12`. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_false_common {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) : False := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_common χ hne hquad heven hGRH
      (by linarith) hlogD hriemann hriemannReciprocal hodd h2
  exact qNeOne_common_sandwich_false_of_twelve hy hbounds.1 hbounds.2

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_false_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) : False := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_neg_one_branch_corrected_common χ hne hquad heven
      hGRH (by linarith) hlogD hriemann hriemannReciprocal hodd h2
  exact qNeOne_common_sandwich_false_of_twelve hy hbounds.1 hbounds.2

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_false_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) : False := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_common χ hne hquad heven hGRH
      (by linarith) hlogD hriemann hriemannReciprocal hodd h2
  exact qNeOne_common_sandwich_false_of_twelve hy hbounds.1 hbounds.2

/-! Conductor-traded c=1 form used by the numerical stage. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_traded {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
          2 * (Real.log y) ^ 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hbase :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch χ hne hquad hGRH hy hriemann hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hmass : AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤ (3 / 20 : ℝ) :=
    AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
  have hleft :
    y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
        2 * (Real.log y) ^ 2 ≤
      y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
        (2 * Real.log y) ^ 2 / 2 := by
    have hmassscaled :
      2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) ≤
        (3 / 10 : ℝ) * (y + 1) := by
      have h := mul_le_mul_of_nonneg_right hmass (by linarith : (0 : ℝ) ≤ y + 1)
      calc
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) =
            2 * (AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1)) :=
          by ring
        _ ≤ 2 * ((3 / 20 : ℝ) * (y + 1)) := mul_le_mul_of_nonneg_left h (by norm_num only)
        _ = (3 / 10 : ℝ) * (y + 1) := by ring
    have h :=
      sub_le_sub_left hmassscaled
        (y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 - (2 * Real.log y) ^ 2 / 2)
    convert h using 1 <;> ring
  have hright :
    (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 ≤
      (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4 := by
    gcongr
  constructor
  · exact hleft.trans hbase.1
  · apply hbase.2.trans
    calc
      _ =
          ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) +
            ((2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter|) :=
        by ring
      _ ≤
          ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) +
            ((2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                  χ.primitiveCharacter|) :=
        add_le_add_left hright _
      _ = _ := by ring

/-! The c=1 even estimate removes the reciprocal `B` witness from the traded upper bound. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_traded {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
          2 * (Real.log y) ^ 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hbase :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_traded χ hne hquad hGRH hy hlogD
      hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_one_branch_at_square_simple χ hne hquad heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlogy)
  constructor
  · exact hbase.1
  · have hBmul := mul_le_mul_of_nonneg_left hB hcoef
    calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                    χ.primitiveCharacter| +
              (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
            11 / 4 :=
        hbase.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
              (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
            11 / 4 :=
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
                ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) :=
            add_le_add hBmul (le_refl _)
          _ = _ := by ring

/-!
Use the strong even reciprocal B estimate to remove the absolute B
witness from the logarithmic upper bound while retaining the same lower bound and witness data.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_traded {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    y ^ 2 - 2 * Real.log (2 * Real.pi) * Real.log y - 1 - (3 / 10 : ℝ) * (y + 1) -
          2 * (Real.log y) ^ 2 ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
          11 / 4 := by
  have hbase :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_traded χ hne hquad hGRH hy hlogD
      hriemann hodd h2
  have hB :=
    primitiveQuadraticBRe_le_of_qneOne_zero_branch_even_at_square_simple χ hne hquad heven hGRH hy
      hlogD hriemannReciprocal hodd h2
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
    exact
      add_nonneg
        (add_nonneg (mul_nonneg (by norm_num only) (le_trans (by norm_num only) hy))
          (by norm_num only))
        (mul_nonneg (by norm_num only) hlogy)
  constructor
  · exact hbase.1
  · have hBmul := mul_le_mul_of_nonneg_left hB hcoef
    calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                    χ.primitiveCharacter| +
              (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
            11 / 4 :=
        hbase.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
              (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) -
            11 / 4 :=
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe
                      χ.primitiveCharacter| +
                ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
                ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) - 11 / 4) :=
            add_le_add hBmul (le_refl _)
          _ = _ := by ring

/-!
Input/assumptions: the c=0 even quadratic branch, GRH, the reciprocal and weighted Riemann
lower bounds, and `log conductor ≤ y` at the square radius.
Conclusion: the exact branch bounds are relaxed to the common numerical `L/U` pair.
Content: the strong B-free upper is weakened using `log π ≥ 1`, while the lower uses
`2 log (2π) ≤ 4`; the resulting bounds use
`PseudoPrime.LLS.Extensions.qNeOneLowerBound` and
`PseudoPrime.LLS.Extensions.qNeOneUpperBound`.
Role: supplies the c=0 member of the common comparison used by the later separation theorem.
-/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_candidate {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
            χ.primitiveCharacter).re ≤
        qNeOneUpperBound y := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_traded χ hne hquad heven hGRH hy
      hlogD hriemann hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
        (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    linarith [Real.log_three_gt_d9]
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 := by linarith [Analysis.log_two_mul_pi_lt]
  constructor
  · have hprod : 2 * Real.log (2 * Real.pi) * Real.log y ≤ 4 * Real.log y := by
      have hmul :=
        mul_le_mul_of_nonneg_right (show 2 * Real.log (2 * Real.pi) ≤ 4 by linarith) hlogy
      linarith
    unfold qNeOneLowerBound
    linarith [hbounds.1]
  · have hprod : (y - Real.log Real.pi) * Real.log y ≤ (y - 1) * Real.log y := by
      have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_left hlogpi y) hlogy
      linarith
    unfold qNeOneUpperBound
    linarith [hbounds.2]

/-! The c=0 candidate sandwich contradicts the two-interval numerical separation. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_false {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) : False := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_traded χ hne hquad heven hGRH hy
      hlogD hriemann hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans hy)
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
        (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    exact (le_trans (by norm_num only) Real.log_three_gt_d9.le).trans h3pi
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 :=
    Analysis.log_two_mul_pi_lt.le.trans (by norm_num only)
  have hlower :
    qNeOneLowerBound y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
          χ.primitiveCharacter).re := by
    have hprod : 2 * Real.log (2 * Real.pi) * Real.log y ≤ 4 * Real.log y := by
      have hmul :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog2pi (by norm_num only : (0 : ℝ) ≤ 2)) hlogy
      exact hmul.trans_eq (by ring)
    unfold qNeOneLowerBound
    linarith [hbounds.1]
  have hupper :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
          χ.primitiveCharacter).re ≤
      qNeOneUpperBound y := by
    have hprod : (y - Real.log Real.pi) * Real.log y ≤ (y - 1) * Real.log y := by
      have := mul_le_mul_of_nonneg_right (sub_le_sub_left hlogpi y) hlogy
      linarith
    unfold qNeOneUpperBound
    linarith [hbounds.2]
  exact
    (not_le_of_gt (qNeOneLowerBound_gt_upperBound hy))
      (hlower.trans hupper)

/-! The c=1 candidate sandwich contradicts the same two-interval numerical separation. -/

theorem primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_false {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) : False := by
  have hbounds :=
    primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_traded χ hne hquad heven hGRH hy
      hlogD hriemann hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
        (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    linarith [Real.log_three_gt_d9]
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 := by linarith [Analysis.log_two_mul_pi_lt]
  have hlower :
    qNeOneLowerBound y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
          χ.primitiveCharacter).re := by
    have hprod : 2 * Real.log (2 * Real.pi) * Real.log y ≤ 4 * Real.log y := by
      have := mul_le_mul_of_nonneg_right (show 2 * Real.log (2 * Real.pi) ≤ 4 by linarith) hlogy
      linarith
    unfold qNeOneLowerBound
    linarith [hbounds.1]
  have hupper :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
          χ.primitiveCharacter).re ≤
      qNeOneUpperBound y := by
    have hprod : (y - Real.log Real.pi) * Real.log y ≤ (y - 1) * Real.log y := by
      have := mul_le_mul_of_nonneg_right (sub_le_sub_left hlogpi y) hlogy
      linarith
    unfold qNeOneUpperBound
    linarith [hbounds.2]
  exact
    (not_le_of_gt (qNeOneLowerBound_gt_upperBound hy))
      (hlower.trans hupper)

end PseudoPrime.LLS.Extensions
