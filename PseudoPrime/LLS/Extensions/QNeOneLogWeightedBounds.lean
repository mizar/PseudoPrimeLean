/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveLogWeightedBounds
public import PseudoPrime.LLS.PrimitiveLogResidueLedger
public import PseudoPrime.LLS.RiemannWeightedBounds
public import PseudoPrime.Analysis.LogarithmicRatios
public import PseudoPrime.LLS.Extensions.QNeOneNumerics
public import PseudoPrime.LLS.Extensions.QNeOneWeightedComparisonInputs
public import PseudoPrime.Analysis.LogarithmicMainTerms
public import PseudoPrime.Analysis.QNeOneElementaryBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.EvenLogWeightedUpper
public import PseudoPrime.Analysis.LogarithmicConstants
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues
public import PseudoPrime.Analysis.ElementaryBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.LLS.Lemma22
public import PseudoPrime.LLS.Extensions.PrimitiveReciprocalRefinedBounds
public import PseudoPrime.LLS.Extensions.PrimitiveReciprocalBranchBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
public import PseudoPrime.LLS.Numerics

/-!
# Even logarithmic bounds and QNeOne comparisons

This module combines the even logarithmic estimates and reciprocal bounds into the three
value-at-two comparisons used by QNeOneConcrete. All three branches use general-character
logarithmic and reciprocal correction estimates.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The Riemann lower envelope with the half-square defect dominates the common
quadratic lower bound for `y ≥ 8`. The certified zero mass and logarithmic constants
supply the two coefficient comparisons used by all three core consumers. -/
theorem qNeOneAnalyticLowerBound_le_riemann_lower {y : ℝ} (hy : 8 ≤ y) :
    qNeOneAnalyticLowerBound y ≤ riemannLogLowerAt (y ^ 2) - (Real.log (y ^ 2)) ^ 2 / 2 := by
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_three_twentieths
      (show 0 ≤ y + 1 by linarith only [hy])
  have hl :=
    mul_le_mul_of_nonneg_right
      (Analysis.log_two_mul_pi_lt.le.trans (show (1839 / 1000 : ℝ) ≤ 2 by norm_num only))
      (Real.log_nonneg (show 1 ≤ y by linarith only [hy]))
  rw [qNeOneAnalyticLowerBound, riemannLogLowerAt, Real.sqrt_sq (by linarith only [hy]),
    Real.log_pow]
  norm_num only
  nlinarith only [hm, hl]

/--
Input/assumptions: the zero branch at `X = y²`, with an even primitive character,
GRH, the weighted Riemann lower bound, and `log conductor ≤ y + log 4`.
Conclusion: the exact even main-error term is retained in the upper contour estimate.
Content: reuse the corrected lower bridge and specialize the exact whole-line generic API at `y²`.
Proof: transfer primitivity and nontriviality to the primitive character, then multiply the
conductor inequality by the nonnegative factor `log y`.
Role: supplies the refined c=0 interface for the B-bound and numerical comparison.
-/
theorem primitiveLogWeightedBounds_of_qneOne_zero_branch_log_four_even_exact {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
          (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcore := weightedComparisonCore_even_zero χ hne heven hGRH hx64 hodd h2
  have hbounds :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le hriemann
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
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
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ ≤ _ := by
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
                ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
                ((1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            add_le_add (le_refl _) (add_le_add hright (le_refl _))
          _ = _ := by ring

/-- For a nonprincipal character with even primitive character, assume GRH, the weighted
Riemann lower bound, `y ≥ 8`, `log conductor ≤ y`, primitive value minus one at two,
and value one on the specified odd primes. Its real weighted sum at `y²` is bounded below
by the negative-one analytic envelope and above by the exact even contour expression
containing `|primitiveBRe|`. Apply the branch lower estimate and the general-character
contour upper estimate, then enlarge the conductor term using `log y ≥ 0`.
This is the input to the reciprocal substitution and correction comparison. -/
theorem primitiveLogWeightedBounds_of_qneOne_neg_one_branch_even_exact_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    qNeOneAnalyticLowerBoundNegOne y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
          (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hlower :=
    characterLogWeightedSum_re_ge_riemann_lower_sub_three_half_log_sq_of_eq_neg_one (y ^ 2) χ
      hriemann (le_trans (by norm_num only) hx64) hodd h2
  rw [hsqrt, hlogsq] at hlower
  have hcore := weightedComparisonCore_even_neg_one χ hne heven hGRH hx64 hodd h2
  have hbounds :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le hriemann
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
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
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ ≤ _ := by
        calc
          _ =
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
                ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            by ring
          _ ≤
              (2 * y + 2 + 2 * Real.log y) *
                  |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
                ((1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
                  Analysis.primitiveLogEvenMainError (y ^ 2)) :=
            add_le_add (le_refl _) (add_le_add hright (le_refl _))
          _ = _ := by ring

/-- For real `y`, define the zero-branch upper envelope as the coefficient
`2y + 2 + 2 log y` times its reciprocal Hadamard-constant bound, plus
`(y + log 4 - log π) log y` and the exact even main error at `y²`.
For the even zero branch with `y ≥ 8` and the stated conductor and character hypotheses,
this bounds the real weighted sum and permits numerical comparison with its lower envelope. -/
noncomputable def qNeOneUpperBoundZeroStar (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundZeroStar y +
    (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
    Analysis.primitiveLogEvenMainError (y ^ 2)

/-- For real `y`, define the negative-one branch upper envelope as the coefficient
`2y + 2 + 2 log y` times its reciprocal Hadamard-constant bound, plus
`(y - log π) log y` and the exact even main error at `y²`.
It bounds the even negative-one branch under its analytic and conductor hypotheses;
adding the correction at two permits comparison with the zero-branch envelope. -/
noncomputable def qNeOneUpperBoundNegOneStar (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundNegOneStar y +
    (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
    Analysis.primitiveLogEvenMainError (y ^ 2)

/-- For real `y`, define the maximum of the zero-branch and one-branch upper envelopes.
Under the respective character hypotheses it also bounds the corrected negative-one sum.
The maximum combines the three comparisons into a single sandwich for the witness argument. -/
noncomputable def qNeOneCommonUpperBound (y : ℝ) : ℝ :=
  max (qNeOneUpperBoundZeroStar y) (qNeOneAnalyticUpperBoundOne y)

/--
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
      mul_pos (by linarith only [Real.pi_lt_d4]) (by positivity)
    have hsq : Real.pi ^ 2 < 16 := by
      rw [show (4 - Real.pi) * (4 + Real.pi) = 16 - Real.pi ^ 2 by ring] at hprodpi
      exact sub_pos.mp hprodpi
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
    have heuler0 : 0 ≤ Real.eulerMascheroniConstant :=
      le_trans (by norm_num only : (0 : ℝ) ≤ 1 / 2) heuler
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
    rw [show Real.log (y ^ 2) = 2 * Real.log y
        by
        rw [Real.log_pow]
        norm_num only]
    have hcondscaled :
      (1 / 2 : ℝ) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) ≤
        (y + 2 / 5) * Real.log y := by
      calc
        (1 / 2 : ℝ) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) =
            (y + Real.log 4 - Real.log Real.pi) * Real.log y :=
          by ring
        _ ≤ (y + 2 / 5) * Real.log y := hcondupper
    have hE' := hE
    rw [show Real.log (y ^ 2) = 2 * Real.log y
        by
        rw [Real.log_pow]
        norm_num only] at hE'
    have hsum := add_le_add (add_le_add hprod hcondscaled) hE'
    simpa only [add_sub_assoc] using hsum
  exact hU.trans_lt hsep

/-- For `12 ≤ y ≤ 13`, the zero-branch upper envelope is strictly below the common lower
envelope. Bound the reciprocal term by its affine estimate and `log y` by the affine
lower estimate anchored at twelve, then verify the resulting polynomial inequality.
This is the first compact-interval separation certificate. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_twelve_thirteen {y : ℝ} (hy : 12 ≤ y)
    (hy13 : y ≤ 13) : qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hloglower : (247 : ℝ) / 100 + 2 / 25 * (y - 12) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (12 : ℝ)) (b := 13) (y := y) (L := 247 / 100)
        (by norm_num only) (by norm_num only) hy hy13 Analysis.log_twelve_gt
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_twelve_thirteen hy hy13
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B hy hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (by linarith only [hy] : (0 : ℝ) ≤ y)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith only [hyl, hL2, sq_nonneg (y - 12), sq_nonneg (y - 13), hy, hy13, hloglower, hB, hLpos]

/-- For `13 ≤ y ≤ 16`, the zero-branch upper envelope is strictly below the common lower
envelope. Obtain the logarithm bound at thirteen from those at two and three, extend it
by an affine lower bound, and combine it with the reciprocal affine estimate.
The resulting polynomial inequality supplies the second compact separation certificate. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_thirteen_sixteen {y : ℝ} (hy : 13 ≤ y)
    (hy16 : y ≤ 16) : qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
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
      Analysis.log_gt_affine_of_anchor (a := (13 : ℝ)) (b := 16) (y := y) (L := 256 / 100)
        (by norm_num only) (by norm_num only) hy hy16 hlog13
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_thirteen_sixteen hy hy16
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith only [hyl, hL2, sq_nonneg (y - 13), sq_nonneg (y - 16), hy, hy16, hloglower, hB, hLpos,
    hlog13]

/-- On `[16,24]`, the zero-branch exact upper envelope is strictly below the common lower.
Use the reciprocal affine bound with constant `23/10` and the logarithm lower bound
anchored at sixteen; the resulting polynomial certificate closes the compact comparison. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_sixteen_twenty_four {y : ℝ}
    (hy : 16 ≤ y) (hy24 : y ≤ 24) : qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hlog16 : (277 : ℝ) / 100 < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    have h2 : (693 : ℝ) / 1000 < Real.log 2 := lt_trans (by norm_num only) Real.log_two_gt_d9
    calc
      (277 : ℝ) / 100 < 2772 / 1000 := by norm_num only
      _ = 4 * (693 / 1000) := by norm_num only
      _ < 4 * Real.log 2 := mul_lt_mul_of_pos_left h2 (by norm_num only)
  have hloglower : (277 : ℝ) / 100 + 1 / 20 * (y - 16) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (16 : ℝ)) (b := 24) (y := y) (L := 277 / 100)
        (by norm_num only) (by norm_num only) hy hy24 hlog16
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_sixteen_twenty_four hy hy24
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith only [hyl, hL2, sq_nonneg (y - 16), sq_nonneg (y - 24), hy, hy24, hloglower, hB, hLpos,
    hlog16]

/-- On `[24,32]`, separate the exact zero-branch upper and common lower envelopes.
The reciprocal affine bound with constant `12/5` and logarithm bound anchored at twenty-four
reduce the relaxed gap to the displayed nonnegative polynomial data. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_twenty_four_thirty_two {y : ℝ}
    (hy : 24 ≤ y) (hy32 : y ≤ 32) : qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
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
      Analysis.log_gt_affine_of_anchor (a := (24 : ℝ)) (b := 32) (y := y) (L := 317 / 100)
        (by norm_num only) (by norm_num only) hy hy32 hlog24
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_twenty_four_thirty_two hy hy32
  apply qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy) hB
  unfold qNeOneAnalyticLowerBound
  ring_nf at ⊢
  have hLpos : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only) hy)
  have hyl := mul_le_mul_of_nonneg_right hloglower (le_trans (by norm_num only) hy)
  have hL2 := mul_le_mul_of_nonneg_right hloglower hLpos
  linarith only [hyl, hL2, sq_nonneg (y - 24), sq_nonneg (y - 32), hy, hy32, hloglower, hB, hLpos,
    hlog24]

/-- On `[32,48]`, the zero-branch upper envelope lies strictly below the common lower.
Lift the reciprocal affine bound with constant `12/5`; `log y ≥ 3` controls the quadratic
and mixed logarithm terms, leaving a strict linear gap. This closes the final compact interval. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound_thirty_two_forty_eight {y : ℝ}
    (hy : 32 ≤ y) (hy48 : y ≤ 48) : qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  have hlog32 : (346 : ℝ) / 100 < Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    have h2 : (693 : ℝ) / 1000 < Real.log 2 := lt_trans (by norm_num only) Real.log_two_gt_d9
    calc
      (346 : ℝ) / 100 < 3465 / 1000 := by norm_num only
      _ = 5 * (693 / 1000) := by norm_num only
      _ < 5 * Real.log 2 := mul_lt_mul_of_pos_left h2 (by norm_num only)
  have hloglower : (346 : ℝ) / 100 + 1 / 40 * (y - 32) ≤ Real.log y := by
    have h :=
      Analysis.log_gt_affine_of_anchor (a := (32 : ℝ)) (b := 48) (y := y) (L := 346 / 100)
        (by norm_num only) (by norm_num only) hy hy48 hlog32
    norm_num only at h ⊢
    exact h.le
  have hB := qNeOneBUpperBoundZeroStar_le_affine_thirty_two_forty_eight hy hy48
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

/-- The five compact c=0 certificates combine with the c=1 bound on `[12,48]`. -/
theorem qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_twelve_forty_eight {y : ℝ} (hy : 12 ≤ y)
    (hy48 : y ≤ 48) : qNeOneCommonUpperBound y < qNeOneAnalyticLowerBound y := by
  have hone :=
    qNeOneAnalyticUpperBoundOne_lt_qNeOneAnalyticLowerBound (y := y)
      (by exact (le_trans (by norm_num only) hy))
  have hzero : qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
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

/-- For `y ≥ 48`, the affine relaxation with reciprocal constant three is strictly below
the analytic lower envelope. The logarithm lower bound gives the positive polynomial gap;
divide that certificate by 300 and rewrite it as the desired envelope difference.
This supplies separation on the unbounded interval. -/
lemma zeroStar_affine_lt_lower {y : ℝ} (hy : 48 ≤ y) :
    (2 * y + 2 + 2 * Real.log y) * (y / 2 - 2 * Real.log y + 3) + (y + 2 / 5) * Real.log y + 2 / 3 -
        (1 / 2) * Real.log y -
        2 * (Real.log y) ^ 2 <
      qNeOneAnalyticLowerBound y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  have hcert := Analysis.affine_log_gap_pos hypos.le (Analysis.zeroStar_log_lower hy hypos)
  apply sub_pos.mp
  exact
    (div_pos hcert (by norm_num only : (0 : ℝ) < 300)).trans_eq
      (by
        unfold qNeOneAnalyticLowerBound
        ring)

end QNeOneZeroStar

/-- For `48 ≤ y`, the zero-branch upper bound is below the analytic lower envelope.
The numerator and affine separation follow from explicit nonnegative polynomial certificates.
This supplies the zero branch of the common-upper-bound separation. -/
theorem qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound {y : ℝ} (hy : 48 ≤ y) :
    qNeOneUpperBoundZeroStar y < qNeOneAnalyticLowerBound y := by
  exact
    qNeOneUpperBoundZeroStar_lt_of_affine_B (le_trans (by norm_num only) hy)
      (Analysis.reciprocal_log_quotient_le_affine hy) (QNeOneZeroStar.zeroStar_affine_lt_lower hy)

/-- For `y ≥ 48`, the common upper envelope is strictly below the analytic lower envelope.
Combine strict separation of its zero-branch and one-branch components with the maximum
inequality. This supplies the unbounded part of the common sandwich contradiction. -/
theorem qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound {y : ℝ} (hy : 48 ≤ y) :
    qNeOneCommonUpperBound y < qNeOneAnalyticLowerBound y := by
  have hzero := qNeOneUpperBoundZeroStar_lt_qNeOneAnalyticLowerBound hy
  have hone :=
    qNeOneAnalyticUpperBoundOne_lt_qNeOneAnalyticLowerBound (y := y)
      (le_trans (by norm_num only : (8 : ℝ) ≤ 48) hy)
  unfold qNeOneCommonUpperBound
  exact max_lt hzero hone

/-- For `y ≥ 12`, the common upper envelope is strictly below the analytic lower envelope.
Use the five compact-interval certificates for `y ≤ 48` and the unbounded certificate
otherwise. This is the numerical separation needed for all three character branches. -/
theorem qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_of_twelve {y : ℝ} (hy : 12 ≤ y) :
    qNeOneCommonUpperBound y < qNeOneAnalyticLowerBound y := by
  by_cases hy48 : y ≤ 48
  · exact qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_twelve_forty_eight hy hy48
  · exact qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound (le_of_lt (lt_of_not_ge hy48))

/-- For `y ≥ 12`, a real value cannot lie between the analytic lower envelope and the common
upper envelope. Compose the two assumed non-strict bounds and contradict strict numerical
separation. This interface applies both to weighted sums and to the corrected sum at two. -/
theorem qNeOne_common_sandwich_false_of_twelve {y z : ℝ} (hy : 12 ≤ y)
    (hlower : qNeOneAnalyticLowerBound y ≤ z) (hupper : z ≤ qNeOneCommonUpperBound y) : False := by
  exact
    (not_lt_of_ge (hlower.trans hupper))
      (qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_of_twelve hy)

/-- Under the even zero-branch hypotheses, GRH, both Riemann lower bounds, `y ≥ 8`,
`log conductor ≤ y + log 4`, and primitive value one on the specified odd primes,
the real weighted sum at `y²` lies between the analytic lower envelope and the zero-branch
upper envelope. Substitute the strong reciprocal Hadamard-constant bound into the exact
contour upper estimate; its multiplying coefficient is nonnegative.
This retains the exact even main error for the corrected negative-one comparison. -/
theorem primitiveLogWeightedBounds_of_qneOne_zero_branch_even_star {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        qNeOneUpperBoundZeroStar y := by
  have hbounds :=
    primitiveLogWeightedBounds_of_qneOne_zero_branch_log_four_even_exact χ hne heven hGRH hy hlogD
      hriemann hodd h2
  have hB :=
    primitiveBRe_le_of_qneOne_zero_branch_even_at_square_log_four_strong χ hne heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only : (1 : ℝ) ≤ 8) hy)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith only [hy, hlogy]
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundZeroStar y +
            (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by
        rw [qNeOneBUpperBoundZeroStar]
        linarith only [hmul]
      _ = qNeOneUpperBoundZeroStar y := by rfl

/-- Under the even zero-branch hypotheses, GRH, both Riemann lower bounds, `y ≥ 8`,
`log conductor ≤ y + log 4`, and primitive value one on the specified odd primes,
the real weighted sum at `y²` lies between the analytic lower and common upper envelopes.
Apply the zero-branch estimate and enlarge its upper bound to the maximum.
This connects the branch to the common numerical contradiction. -/
theorem primitiveLogWeightedBounds_of_qneOne_zero_branch_even_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        qNeOneCommonUpperBound y := by
  have h :=
    primitiveLogWeightedBounds_of_qneOne_zero_branch_even_star χ hne heven hGRH hy hlogD hriemann
      hriemannReciprocal hodd h2
  constructor
  · exact h.1
  · exact
      h.2.trans
        (show qNeOneUpperBoundZeroStar y ≤ qNeOneCommonUpperBound y
          by
          unfold qNeOneCommonUpperBound
          exact le_max_left _ _)

/-- Under the even negative-one branch hypotheses, GRH, both Riemann lower bounds,
`y ≥ 8`, `log conductor ≤ y`, and primitive value one on the specified odd primes,
the real weighted sum at `y²` lies between the negative-one analytic lower envelope
and its explicit upper envelope. Multiply the reciprocal Hadamard-constant bound by the
nonnegative contour coefficient and preserve the exact even main error.
This supplies the upper estimate before adding the correction at two. -/
theorem primitiveLogWeightedBounds_of_qneOne_neg_one_branch_even_star {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        qNeOneUpperBoundNegOneStar y := by
  have hbounds :=
    primitiveLogWeightedBounds_of_qneOne_neg_one_branch_even_exact_le χ hne heven hGRH hy hlogD
      hriemann hodd h2
  have hB :=
    primitiveBRe_le_of_qneOne_neg_one_branch_at_square_le χ hne heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only : (1 : ℝ) ≤ 8) hy)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith only [hy, hlogy]
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * qNeOneBUpperBoundNegOneStar y +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by
        rw [qNeOneBUpperBoundNegOneStar]
        linarith only [hmul]
      _ = qNeOneUpperBoundNegOneStar y := by rfl

/-- For `y ≥ 8`, compute the difference between the zero-branch upper envelope and the
negative-one upper envelope plus `logTwoSquareCorrection y`. The result is
`(2y + 2 + 2 log y) * log 2 * (2/3 - 1/y²)/(1 - 1/y)² + (log 2)²`.
Cancel the common exact even main error and use the reciprocal-envelope difference.
Its nonnegative terms permit comparison of the corrected branch with the zero branch. -/
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
      have hy1 : (1 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
      simpa only [one_mul] using hy1
    positivity
  have hB := qNeOneBUpperBoundZeroStar_sub_negOneStar_eq hy
  rw [qNeOneUpperBoundZeroStar, qNeOneUpperBoundNegOneStar, Analysis.logTwoSquareCorrection, hlog4]
  calc
    _ =
        (2 * y + 2 + 2 * Real.log y) *
            (qNeOneBUpperBoundZeroStar y - qNeOneBUpperBoundNegOneStar y) +
          (Real.log 2) ^ 2 :=
      by ring_nf
    _ = _ := by rw [hB]

/-- Under the even negative-one branch hypotheses, GRH, both Riemann lower bounds,
`y ≥ 8`, `log conductor ≤ y`, and primitive value one on the specified odd primes,
the corrected weighted value `Re S + logTwoSquareCorrection y` lies between the common
analytic lower envelope and the zero-branch upper envelope. The corrected arithmetic lower
estimate supplies the first inequality; the explicit nonnegative envelope gap supplies
the second. This places the negative-one branch in the same comparison as the zero branch. -/
theorem primitiveLogWeightedBounds_of_qneOne_neg_one_branch_corrected_star {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ≤
        qNeOneUpperBoundZeroStar y := by
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hcore := weightedComparisonCore_even_neg_one χ hne heven hGRH hx hodd h2
  have hc :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le hriemann hriemannReciprocal
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hlow :
    qNeOneAnalyticLowerBound y - Analysis.logTwoSquareCorrection y ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2)
          χ.primitiveCharacter).re := by
    have hl := qNeOneAnalyticLowerBound_le_riemann_lower hy
    have hs := hc.1
    rw [Analysis.logTwoSquareCorrection]
    rw [Real.log_pow] at hl hs
    norm_num only at hl hs
    linarith only [hl, hs]
  have hupp :=
    primitiveLogWeightedBounds_of_qneOne_neg_one_branch_even_star χ hne heven hGRH hy hlogD hriemann
      hriemannReciprocal hodd h2
  have hdiff := qNeOneUpperBoundZeroStar_sub_negOneStar_add_delta_eq hy
  constructor
  · exact sub_le_iff_le_add.mp hlow
  · have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
    have hsqpos : 0 < y ^ 2 := sq_pos_of_pos hypos
    have hfactor : 0 ≤ 2 / 3 - 1 / y ^ 2 := by
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hsqpos).2
      have hy2 : (64 : ℝ) ≤ y ^ 2 := by
        have h :=
          mul_le_mul hy hy (by norm_num only : (0 : ℝ) ≤ 8) (by linarith only [hy] : (0 : ℝ) ≤ y)
        norm_num only at h
        simpa only [pow_two] using h
      calc
        (1 : ℝ) ≤ (2 / 3 : ℝ) * 64 := by norm_num only
        _ ≤ (2 / 3 : ℝ) * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (by norm_num only)
    have hdenpos : 0 < (1 - 1 / y) ^ 2 :=
      sq_pos_of_pos
        (sub_pos.mpr ((div_lt_one hypos).2 (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 8) hy)))
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num only)
    have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only : (1 : ℝ) ≤ 8) hy)
    have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith only [hy, hlogy]
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

/-- Under the even negative-one branch hypotheses, GRH, both Riemann lower bounds,
`y ≥ 8`, `log conductor ≤ y`, and primitive value one on the specified odd primes,
the corrected value `Re S + logTwoSquareCorrection y` lies between the analytic lower
and common upper envelopes. First compare it with the zero-branch upper envelope, then
enlarge to the maximum. This supplies the corrected branch's common sandwich. -/
theorem primitiveLogWeightedBounds_of_qneOne_neg_one_branch_corrected_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re +
          Analysis.logTwoSquareCorrection y ≤
        qNeOneCommonUpperBound y := by
  have h :=
    primitiveLogWeightedBounds_of_qneOne_neg_one_branch_corrected_star χ hne heven hGRH hy hlogD
      hriemann hriemannReciprocal hodd h2
  constructor
  · exact h.1
  · exact
      h.2.trans
        (show qNeOneUpperBoundZeroStar y ≤ qNeOneCommonUpperBound y
          by
          unfold qNeOneCommonUpperBound
          exact le_max_left _ _)

/--
Input/assumptions: the c=1 branch at `X = y²`, an even primitive character, GRH,
the weighted Riemann lower bound, and `log conductor ≤ y`.
Conclusion: the c=1 branch is connected to the exact whole-line upper with the analytic lower
bound and the retained even main-error term.
Content: normalize the existing c=1 lower estimate and specialize the exact generic upper.
Role: supplies the exact c=1 interface before the reciprocal B substitution.
-/
theorem primitiveLogWeightedBounds_of_qneOne_one_branch_even_exact {q : ℕ}
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    qNeOneAnalyticLowerBound y ≤
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        (2 * y + 2 + 2 * Real.log y) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
          (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
          Analysis.primitiveLogEvenMainError (y ^ 2) := by
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by norm_num only) hy
  have hx64 : (64 : ℝ) ≤ y ^ 2 := Analysis.sq_ge_64_of_ge_8 hy
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcore := weightedComparisonCore_even_one χ hne heven hGRH hx64 hodd h2
  have hbounds :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le hriemann
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
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
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            (1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hupper
      _ =
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            ((1 / 2) * (Real.log χ.conductor - Real.log Real.pi) * (2 * Real.log y) +
              Analysis.primitiveLogEvenMainError (y ^ 2)) :=
        by ring
      _ ≤ _ := add_le_add (le_refl _) (add_le_add hright (le_refl _))
      _ = _ := by ring

/-- Under the even one-branch hypotheses, GRH, both Riemann lower bounds, `y ≥ 8`,
`log conductor ≤ y`, and primitive value one on the specified odd primes,
the real weighted sum at `y²` lies between the analytic lower envelope and the explicit
one-branch upper envelope. Substitute the square-radius reciprocal Hadamard-constant bound
into the exact upper estimate, using the nonnegative contour coefficient.
This supplies the one branch of the common envelope comparison. -/
theorem primitiveLogWeightedBounds_of_qneOne_one_branch_even_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        qNeOneAnalyticUpperBoundOne y := by
  have hbounds :=
    primitiveLogWeightedBounds_of_qneOne_one_branch_even_exact χ hne heven hGRH hy hlogD hriemann
      hodd h2
  have hB :=
    primitiveBRe_le_of_qneOne_one_branch_at_square_simple χ hne heven hGRH hy hlogD
      hriemannReciprocal hodd h2
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (le_trans (by norm_num only : (1 : ℝ) ≤ 8) hy)
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith only [hy, hlogy]
  have hmul := mul_le_mul_of_nonneg_left hB hcoef
  constructor
  · exact hbounds.1
  · calc
      _ ≤
          (2 * y + 2 + 2 * Real.log y) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        hbounds.2
      _ ≤
          (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
            (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
            Analysis.primitiveLogEvenMainError (y ^ 2) :=
        by linarith only [hmul]
      _ = qNeOneAnalyticUpperBoundOne y := by
        unfold qNeOneAnalyticUpperBoundOne
        rw [Analysis.primitiveLogEvenMainError]

/-- Under the even one-branch hypotheses, GRH, both Riemann lower bounds, `y ≥ 8`,
`log conductor ≤ y`, and primitive value one on the specified odd primes,
the real weighted sum at `y²` lies between the analytic lower and common upper envelopes.
Apply the one-branch analytic estimate and enlarge its upper bound to the maximum.
This connects the one branch to the common numerical contradiction. -/
theorem primitiveLogWeightedBounds_of_qneOne_one_branch_even_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
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
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ∧
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ.primitiveCharacter).re ≤
        qNeOneCommonUpperBound y := by
  have h :=
    primitiveLogWeightedBounds_of_qneOne_one_branch_even_analytic χ hne heven hGRH hy hlogD hriemann
      hriemannReciprocal hodd h2
  constructor
  · exact h.1
  · exact
      h.2.trans
        (show qNeOneAnalyticUpperBoundOne y ≤ qNeOneCommonUpperBound y
          by
          unfold qNeOneCommonUpperBound
          exact le_max_right _ _)

end PseudoPrime.LLS.Extensions
