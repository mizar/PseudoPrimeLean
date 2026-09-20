/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Extensions.QNeOneCorrections
import PseudoPrime.LLS.WeightedComparison
import PseudoPrime.LLS.Extensions.EvenWeightedComparison

/-!
# The independent `QNeOne` branch's log/reciprocal defects (CP07)

This file connects the existing three-branch `χ̃(2) ∈ {0, 1, -1}` two-adic correction estimates
(`QNeOneCorrections.lean`, `TwoAdicCorrections.lean`) to the common core `LLSWeightedComparisonCore`
from CP06, by rephrasing them as bounds on `weightedLogDefect`/`weightedReciprocalDefect`.

The odd-prime-triviality hypothesis `hodd` (every odd prime power below the reindexed cutoff has
character value `1`) already gives the *exact* identity
`weightedLogDefect χ.primitiveCharacter x = twoAdicLogCorrection x χ`
(`logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one`): the
defect's support is limited to powers of `2`. This is the "the defect's support is limited to
powers of 2" step of CP07's independent-branch checklist. The three branches below then supply
`dS`, `dR` for `LLSWeightedComparisonCore` by bounding this two-adic correction, distinguishing the
`c = 1` branch's exact `0` local correction from the coarser `c = 0`/`c = -1` bounds.
-/

namespace PseudoPrime.LLS.Extensions

open AnalyticNumberTheory.Arithmetic

/-- The odd-prime-triviality hypothesis used throughout the `QNeOne` two-adic branches: every odd
prime appearing in the reindexed two-adic-correction range has primitive-character value `1`. -/
abbrev OddPrimeTrivial {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : Prop :=
  ∀ {k p : ℕ},
    k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
      p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → χ.primitiveCharacter p = 1

/-- `χ̃(2) = 0` branch: the log-weighted defect of the primitive character is at most
`(log x)² / 2`, supplying `dS` for `LLSWeightedComparisonCore` on this branch. -/
theorem weightedLogDefect_le_of_apply_two_eq_zero {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hx : 2 ≤ x) (hodd : OddPrimeTrivial χ x)
    (h2 : χ.primitiveCharacter 2 = 0) :
    LLS.weightedLogDefect χ.primitiveCharacter x ≤ (Real.log x) ^ 2 / 2 := by
  rw [LLS.weightedLogDefect,
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ hx
      hodd]
  exact
    twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_zero x χ
      (ne_of_gt (lt_of_lt_of_le (by norm_num only) hx)) h2

/-- `χ̃(2) = 0` branch: the reciprocal-weighted defect is at most `log 2`, supplying `dR`. -/
theorem weightedReciprocalDefect_le_of_apply_two_eq_zero {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hx : 2 ≤ x) (hodd : OddPrimeTrivial χ x)
    (h2 : χ.primitiveCharacter 2 = 0) :
    LLS.weightedReciprocalDefect χ.primitiveCharacter x ≤ Real.log 2 := by
  rw [LLS.weightedReciprocalDefect,
    reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one x χ hx hodd]
  exact
    twoAdicReciprocalCorrection_le_log_two_of_apply_two_eq_zero x χ
      (lt_of_lt_of_le (by norm_num only) hx) h2

/-- `χ̃(2) = 1` branch: the log-weighted defect is at most `(log x)² / 2` (kept alongside the
`c = 0` branch's shared envelope), even though the two-adic correction itself is exactly `0`. -/
theorem weightedLogDefect_le_of_apply_two_eq_one {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hquad : χ.primitiveCharacter.IsQuadratic) (hx : 2 ≤ x)
    (hodd : OddPrimeTrivial χ x) (h2 : χ.primitiveCharacter 2 = 1) :
    LLS.weightedLogDefect χ.primitiveCharacter x ≤ (Real.log x) ^ 2 / 2 := by
  rw [LLS.weightedLogDefect,
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ hx
      hodd]
  exact
    twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_one x χ hquad
      (ne_of_gt (lt_of_lt_of_le (by norm_num only) hx)) h2

/--
Input/assumptions: `χ̃(2) = 1` and `χ̃` quadratic.
Conclusion: the reciprocal-weighted defect is exactly `0`.
Content: `twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one` gives the local correction
itself vanishes, distinguishing this branch's exact `dR = 0` from the coarser bounds on the other
two branches.
Role: supplies the sharpest possible `dR` for `LLSWeightedComparisonCore` on the `c = 1` branch.
-/
theorem weightedReciprocalDefect_eq_zero_of_apply_two_eq_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hquad : χ.primitiveCharacter.IsQuadratic)
    (hx : 2 ≤ x) (hodd : OddPrimeTrivial χ x) (h2 : χ.primitiveCharacter 2 = 1) :
    LLS.weightedReciprocalDefect χ.primitiveCharacter x = 0 := by
  rw [LLS.weightedReciprocalDefect,
    reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one x χ hx hodd,
    twoAdicReciprocalCorrection_eq_zero_of_apply_two_eq_one x χ hquad h2]

/-- `χ̃(2) = -1` branch: the log-weighted defect is at most `(log x)² / 2 + log 2 * (log x -
log 2)`, the sharpened envelope (valid for `x ≥ 4`) used by the corrected odd branch instead of
the coarser `(3/2)(log x)²` bound. -/
theorem weightedLogDefect_le_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hquad : χ.primitiveCharacter.IsQuadratic) (hx : 4 ≤ x)
    (hodd : OddPrimeTrivial χ x) (h2 : χ.primitiveCharacter 2 = -1) :
    LLS.weightedLogDefect χ.primitiveCharacter x ≤
      (Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2) := by
  rw [LLS.weightedLogDefect,
    logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ
      (by linarith) hodd]
  exact
    twoAdicLogCorrection_le_half_log_sq_add_log_two_mul_log_half_of_apply_two_eq_neg_one x χ hquad
      hx h2

/-- `χ̃(2) = -1` branch: the reciprocal-weighted defect is at most `(4/3) log 2`. -/
theorem weightedReciprocalDefect_le_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hquad : χ.primitiveCharacter.IsQuadratic)
    (hx : 2 ≤ x) (hodd : OddPrimeTrivial χ x) (h2 : χ.primitiveCharacter 2 = -1) :
    LLS.weightedReciprocalDefect χ.primitiveCharacter x ≤ (4 / 3) * Real.log 2 := by
  rw [LLS.weightedReciprocalDefect,
    reciprocalWeightedSum_sub_re_eq_twoAdicCorrection_of_eq_one x χ hx hodd]
  exact twoAdicReciprocalCorrection_le_four_thirds_log_two_of_apply_two_eq_neg_one x χ hquad hx h2

/-- The even `χ̃(2)=0` branch supplies every field of the common comparison core.
At `X ≥ 64`, its defects are bounded by `(log X)^2/2` and `log 2`, while the
exact even error is preserved for the numerical comparison. -/
theorem weightedComparisonCore_even_zero {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hne : χ ≠ 1) (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 64 ≤ X)
    (hodd : OddPrimeTrivial χ X) (h2 : χ.primitiveCharacter 2 = 0) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|
      ((Real.log X) ^ 2 / 2) (Real.log 2) (Analysis.primitiveLogEvenMainError X) := by
  have hx : 2 ≤ X := le_trans (by norm_num only) hX
  exact
    weightedComparisonCore_even_of_grh χ hne hquad heven hGRH hX
      (weightedLogDefect_le_of_apply_two_eq_zero X χ hx hodd h2)
      (weightedReciprocalDefect_le_of_apply_two_eq_zero X χ hx hodd h2)

/-- The even `χ̃(2)=1` branch constructs the same core with reciprocal defect zero.
The logarithmic defect keeps the envelope used by the existing numerical comparison;
no approximation is made to the even logarithmic error. -/
theorem weightedComparisonCore_even_one {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hne : χ ≠ 1) (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 64 ≤ X)
    (hodd : OddPrimeTrivial χ X) (h2 : χ.primitiveCharacter 2 = 1) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|
      ((Real.log X) ^ 2 / 2) 0 (Analysis.primitiveLogEvenMainError X) := by
  have hx : 2 ≤ X := le_trans (by norm_num only) hX
  exact
    weightedComparisonCore_even_of_grh χ hne hquad heven hGRH hX
      (weightedLogDefect_le_of_apply_two_eq_one X χ hquad hx hodd h2)
      (weightedReciprocalDefect_eq_zero_of_apply_two_eq_one X χ hquad hx hodd h2).le

/-- The even `χ̃(2)=-1` branch supplies the sharpened logarithmic defect and
the reciprocal defect `(4/3) log 2`. The resulting common core retains the exact
even error and is consumed by the corrected three-branch comparison. -/
theorem weightedComparisonCore_even_neg_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hne : χ ≠ 1) (hquad : χ.primitiveCharacter.IsQuadratic)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 64 ≤ X)
    (hodd : OddPrimeTrivial χ X) (h2 : χ.primitiveCharacter 2 = -1) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|
      ((Real.log X) ^ 2 / 2 + Real.log 2 * (Real.log X - Real.log 2)) ((4 / 3) * Real.log 2)
      (Analysis.primitiveLogEvenMainError X) := by
  exact
    weightedComparisonCore_even_of_grh χ hne hquad heven hGRH hX
      (weightedLogDefect_le_of_apply_two_eq_neg_one X χ hquad (le_trans (by norm_num only) hX) hodd
        h2)
      (weightedReciprocalDefect_le_of_apply_two_eq_neg_one X χ hquad
        (le_trans (by norm_num only) hX) hodd h2)

end PseudoPrime.LLS.Extensions
