/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Theorem11S1FullLevel
import PseudoPrime.Analysis.QNeOneElementaryBounds
import PseudoPrime.LLS.Lemma23
import PseudoPrime.LLS.Extensions.QNeOneCorrections
import PseudoPrime.LLS.Extensions.PrimitiveQuadraticReciprocalContour

/-!
# Quadratic reciprocal estimate for the level-indexed API

Connects the quadratic reciprocal estimate to `LLSPart1PrimitiveReciprocalExplicitFormulaRawAt` and
absorbs
the conductor correction into the level. The contour-dependent results are kept in this extension
module to avoid an import cycle in the basic lemma module.
-/

namespace PseudoPrime.LLS.Extensions

/-!
The Q_ne1 no-witness branch supplies the reciprocal lower input needed to turn the raw
quadratic residue estimate into an explicit bound for `|Re B(χ)|`.
-/

/-- The `χ̃(2)=0` Q_ne1 branch yields the reciprocal raw-formula bound for `|Re B(χ)|`. -/
theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x)
    (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 1 / 4 -
          (Real.log x - 8 / 5 - Real.log 2)) /
        (1 - 1 / Real.sqrt x) ^ 2 := by
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hraw :=
    primitiveQuadraticReciprocalRaw' χ.primitiveCharacter hprimitive hprimne hquad hGRH hx
  have hlogdiv : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast χ.conductor_ne_zero) Real.pi_ne_zero
  rw [hlogdiv] at hraw
  have hlower :=
    characterReciprocalWeightedSum_re_ge_log_sub_eight_fifths_sub_log_two_of_eq_zero x χ hriemann
      (by linarith) hodd h2
  have hsqrt : 1 < Real.sqrt x := by
    have hxone : (1 : ℝ) < x := by linarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    nlinarith only [hxone, hsqrt_nonneg, hsqrt_sq]
  have hden : 0 < (1 - 1 / Real.sqrt x) ^ 2 := by
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hpos : 0 < 1 - 1 / Real.sqrt x := by
      have hdiv : 1 / Real.sqrt x < 1 := by
        apply (div_lt_iff₀ hsqrtpos).2
        linarith
      linarith
    positivity
  apply (le_div_iff₀ hden).2
  have hbd :
    (1 - 1 / Real.sqrt x) ^ 2 *
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 1 / 4 -
        (Real.log x - 8 / 5 - Real.log 2) := by
    linarith [hraw, hlower]
  simpa only [one_div, mul_comm, ge_iff_le] using hbd

/-! The `χ̃(2)=1` reciprocal lower bound is stronger than the c=0 bound. -/

theorem primitiveQuadraticBRe_le_of_qneOne_one_branch {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x)
    (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
          (Real.log x - 8 / 5 - Real.log 2)) /
        (1 - 1 / Real.sqrt x) ^ 2 := by
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
  have hraw :=
    primitiveQuadraticReciprocalRaw_even_le
      (show 2 ≤ χ.conductor
        by
        have hN1 : χ.conductor ≠ 1 :=
          AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprimne
        have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
        omega)
      hGRH hprimitive hprimne hinv hquad heven hx
  have hlower :=
    characterReciprocalWeightedSum_re_ge_log_sub_eight_fifths_of_eq_one x χ hquad hriemann
      (by linarith) hodd h2
  have hsqrt : 1 < Real.sqrt x := by
    have hxone : (1 : ℝ) < x := by linarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    nlinarith only [hxone, hsqrt_nonneg, hsqrt_sq]
  have hden : 0 < (1 - 1 / Real.sqrt x) ^ 2 := by
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hpos : 0 < 1 - 1 / Real.sqrt x := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hsqrtpos).2
      linarith
    positivity
  apply (le_div_iff₀ hden).2
  have hbd :
    (1 - 1 / Real.sqrt x) ^ 2 *
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (Real.log x - 8 / 5 - Real.log 2) := by
    linarith [hraw, hlower, Real.log_pos one_lt_two]
  simpa only [one_div, mul_comm, ge_iff_le] using hbd

/-!
The even Q-ne-one branch retains the stronger `-4/5` reciprocal remainder.  The π term is kept
explicit here; the later square specialization may trade it against a conductor bound.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch_even {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x)
    (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
          (Real.log x - 8 / 5 - Real.log 2)) /
        (1 - 1 / Real.sqrt x) ^ 2 := by
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
  have hraw :=
    primitiveQuadraticReciprocalRaw_even_le
      (show 2 ≤ χ.conductor
        by
        have hN1 : χ.conductor ≠ 1 :=
          AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprimne
        have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
        omega)
      hGRH hprimitive hprimne hinv hquad heven hx
  have hlower :=
    characterReciprocalWeightedSum_re_ge_log_sub_eight_fifths_sub_log_two_of_eq_zero x χ hriemann
      (by linarith) hodd h2
  have hsqrt : 1 < Real.sqrt x := by
    have hxone : (1 : ℝ) < x := by linarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    nlinarith only [hxone, hsqrt_nonneg, hsqrt_sq]
  have hden : 0 < (1 - 1 / Real.sqrt x) ^ 2 := by
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hpos : 0 < 1 - 1 / Real.sqrt x := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hsqrtpos).2
      linarith
    positivity
  apply (le_div_iff₀ hden).2
  have hbd :
    (1 - 1 / Real.sqrt x) ^ 2 *
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (Real.log x - 8 / 5 - Real.log 2) := by
    linarith [hraw, hlower]
  simpa only [one_div, mul_comm, ge_iff_le] using hbd

/-- The same Q_ne1 bound specialized to `x = y²` and `log D ≤ y`. -/
theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch_at_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * y - 1 / 4 - (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hx : 64 ≤ y ^ 2 := by nlinarith
  have hbase := primitiveQuadraticBRe_le_of_qneOne_zero_branch χ hne hquad hGRH hx hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have : 0 ≤ 1 - 1 / y ^ 2 := by
      have : 1 ≤ y ^ 2 := by nlinarith
      have : 1 / y ^ 2 ≤ 1 := by
        apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
        nlinarith
      linarith
    positivity
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 1 / 4 -
        (Real.log (y ^ 2) - 8 / 5 - Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * y - 1 / 4 - (2 * Real.log y - 8 / 5 - Real.log 2) := by
    rw [hlogsq]
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have hmul' := le_trans hmul (mul_le_mul_of_nonneg_left (sub_le_self _ hpi) hcoef)
    convert
        sub_le_sub_right (sub_le_sub_right hmul' (1 / 4 : ℝ))
          (2 * Real.log y - 8 / 5 - Real.log 2) using
        1
  rw [hsqrt] at hbase
  rw [hlogsq] at hbase
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have : 0 < 1 - 1 / y := by
      have : 1 / y < 1 := by
        apply (div_lt_iff₀ hypos).2
        linarith
      linarith
    positivity
  rw [hlogsq] at hnum
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 1 / 4 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hbase
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum

/-!
Input/assumptions: the quadratic c=0 branch at `X = y²`, with `y ≥ 8` and
`log conductor ≤ y + log 4`.
Conclusion: retain the fixed `log 4` conductor penalty in the explicit `B` bound.
Content: specialize the parity-uniform reciprocal bound; no evenness assumption is required.
The conductor penalty remains explicit in the radius variable `y`.
Proof: specialize the raw bound at `y²`, simplify the square root and logarithm, and multiply the
conductor inequality by the nonnegative reciprocal coefficient.
Role: the input for the c=0 analytic upper bound.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch_at_square_log_four {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 1 / 4 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hx : 64 ≤ y ^ 2 := by nlinarith
  have hbase := primitiveQuadraticBRe_le_of_qneOne_zero_branch χ hne hquad hGRH hx hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hnonneg : 0 ≤ 1 - 1 / y ^ 2 := by
      have hy2 : 1 ≤ y ^ 2 := by nlinarith
      have hinv : 1 / y ^ 2 ≤ 1 := by
        apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
        nlinarith
      linarith
    positivity
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 1 / 4 -
        (Real.log (y ^ 2) - 8 / 5 - Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 1 / 4 -
        (2 * Real.log y - 8 / 5 - Real.log 2) := by
    rw [hlogsq]
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    nlinarith
  rw [hsqrt] at hbase
  rw [hlogsq] at hbase
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  rw [hlogsq] at hnum
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 1 / 4 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hbase
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum

/-!
Input/assumptions: the even quadratic one-branch hypotheses and `X = y²`, with `y ≥ 8` and
`log conductor ≤ y`.
Conclusion: the c=1 reciprocal `B` estimate is simplified to the coefficient form used by the
Q-ne-one upper bound.
Content: the proof reuses the c=1 retained-π estimate and the same elementary coefficient
comparison as the zero branch.
Proof: clear the positive denominator and apply the logarithmic and numerical bounds.
Role: input to `primitiveQuadraticLogWeightedBounds_of_qneOne_one_branch_even_traded`.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_one_branch_at_square_simple {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1) := by
  have hypos : 0 < y := by linarith
  have hstrong :=
    primitiveQuadraticBRe_le_of_qneOne_one_branch χ hne hquad heven hGRH (by nlinarith : 64 ≤ y ^ 2)
      hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  rw [hsqrt, hlogsq] at hstrong
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  have hlog_upper : Real.log y ≤ y / 8 + 3 * Real.log 2 - 1 := by
    have hquot : 0 < y / 8 := by positivity
    have hlog := Real.log_le_sub_one_of_pos hquot
    have hmul : (y / 8) * 8 = y := by ring
    have hlogmul := Real.log_mul (ne_of_gt hquot) (by norm_num only : (8 : ℝ) ≠ 0)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only
    have hylog : Real.log y = Real.log (y / 8) + Real.log 8 := by
      calc
        Real.log y = Real.log ((y / 8) * 8) := by rw [hmul]
        _ = _ := hlogmul
    rw [hylog, hlog8]
    linarith
  have hlog_lower : 3 * Real.log 2 ≤ Real.log y := by
    have h28 :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (2 : ℝ) by norm_num only)
        (show 0 < (8 : ℝ) by norm_num only) (by norm_num only : (2 : ℝ) ≤ 8)
    have h8y :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (8 : ℝ) by norm_num only) (show 0 < y by linarith)
        hy
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only
    linarith
  have hlog2_lower : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_upper : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hlogpi_lower : 1.098 < Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
        (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    linarith [Real.log_three_gt_d9]
  have hlogpi_upper : Real.log Real.pi ≤ 1.4 := by
    have hp4 :=
      Real.strictMonoOn_log.monotoneOn (show 0 < Real.pi by positivity)
        (show 0 < (4 : ℝ) by norm_num only) (le_of_lt Real.pi_lt_four)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only
    linarith [Real.log_two_lt_d9]
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hsq : 1 ≤ y ^ 2 := by nlinarith
    have hinv : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith
    have : 0 ≤ 1 - 1 / y ^ 2 := by linarith
    positivity
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2) := by
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    linarith
  have hcoeff :=
    Analysis.reciprocal_square_coefficient_nonneg hy hlog_upper hlog_lower hlog2_lower
      hlog2_upper hypos
  have hcompare :
    ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 ≤
      (1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1) := by
    apply (div_le_iff₀ hden).2
    have heq :
      (1 - 1 / y) ^ 2 * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) -
          ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) =
        (0.45 - Real.log 2 + Real.log Real.pi / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - Real.log Real.pi / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 := by
      field_simp
      ring
    have hpi_lower : 0 ≤ (Real.log Real.pi - 1.098) / 2 := by linarith
    have hpi_upper : 0 ≤ (1.4 - Real.log Real.pi) / (2 * y ^ 2) := by positivity
    have heq2 :
      (0.45 - Real.log 2 + Real.log Real.pi / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - Real.log Real.pi / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 =
        (0.45 - Real.log 2 + 1.098 / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - 1.4 / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 +
          (Real.log Real.pi - 1.098) / 2 +
          (1.4 - Real.log Real.pi) / (2 * y ^ 2) := by
      field_simp
      ring
    have hE :
      0 ≤
        (0.45 - Real.log 2 + Real.log Real.pi / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - Real.log Real.pi / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 := by
      rw [heq2]
      linarith
    nlinarith only [hE, heq]
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hstrong
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      (div_le_div_iff_of_pos_right hden).2 hnum
    _ ≤ _ := hcompare

/-! The strong even reciprocal B bound at `X = y²`, retaining the π contribution. -/

theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch_even_at_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hx : 64 ≤ y ^ 2 := by nlinarith
  have hbase :=
    primitiveQuadraticBRe_le_of_qneOne_zero_branch_even χ hne hquad heven hGRH hx hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hsq : 1 ≤ y ^ 2 := by nlinarith
    have hinv : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith
    have : 0 ≤ 1 - 1 / y ^ 2 := by linarith
    positivity
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (Real.log (y ^ 2) - 8 / 5 - Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2) := by
    rw [hlogsq]
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    linarith
  rw [hsqrt, hlogsq] at hbase
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  rw [hlogsq] at hnum
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hbase
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum

/-!
The c=0 strong reciprocal bound with the actual `log conductor ≤ y + log 4` premise.
The `-4/5` remainder is retained, so this is the B₀* input for the bound comparison and does not
reuse the invalid `log conductor ≤ y` candidate.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch_even_at_square_log_four_strong {N : ℕ}
    [NeZero N] (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hx : 64 ≤ y ^ 2 := by nlinarith
  have hbase :=
    primitiveQuadraticBRe_le_of_qneOne_zero_branch_even χ hne hquad heven hGRH hx hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hsq : 1 ≤ y ^ 2 := by nlinarith
    have hinv : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith
    have : 0 ≤ 1 - 1 / y ^ 2 := by linarith
    positivity
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (Real.log (y ^ 2) - 8 / 5 - Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2) := by
    rw [hlogsq]
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    linarith
  rw [hsqrt, hlogsq] at hbase
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  rw [hlogsq] at hnum
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hbase
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum

/-!
Input/assumptions: the even quadratic zero-branch hypotheses and `X = y²`, with `y ≥ 8` and
`log conductor ≤ y`.
Conclusion: the strong reciprocal `B` estimate is simplified to the coefficient form used by
the Q-ne-one upper bound.
Content: the comparison uses `log y ≤ y/8 + 3 log 2 - 1`, `3 log 2 ≤ log y`, and the
elementary bounds `0.69 ≤ log 2 < 0.7`, `1.098 < log π ≤ 1.4`.
Proof: apply the retained-π square estimate and compare its numerator with the target after
clearing the positive denominator.
Role: input to `primitiveQuadraticLogWeightedBounds_of_qneOne_zero_branch_even_traded`.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_zero_branch_even_at_square_simple {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1) := by
  have hypos : 0 < y := by linarith
  have hstrong :=
    primitiveQuadraticBRe_le_of_qneOne_zero_branch_even_at_square χ hne hquad heven hGRH hy hlogD
      hriemann hodd h2
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  have hlog_upper : Real.log y ≤ y / 8 + 3 * Real.log 2 - 1 := by
    have hquot : 0 < y / 8 := by positivity
    have hlog := Real.log_le_sub_one_of_pos hquot
    have hmul : (y / 8) * 8 = y := by ring
    have hlogmul := Real.log_mul (ne_of_gt hquot) (by norm_num only : (8 : ℝ) ≠ 0)
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only
    have hylog : Real.log y = Real.log (y / 8) + Real.log 8 := by
      calc
        Real.log y = Real.log ((y / 8) * 8) := by rw [hmul]
        _ = _ := hlogmul
    rw [hylog, hlog8]
    linarith
  have hlog_lower : 3 * Real.log 2 ≤ Real.log y := by
    have h28 :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (2 : ℝ) by norm_num only)
        (show 0 < (8 : ℝ) by norm_num only) (by norm_num only : (2 : ℝ) ≤ 8)
    have h8y :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (8 : ℝ) by norm_num only) (show 0 < y by linarith)
        hy
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only
    linarith
  have hlog2_lower : 0.69 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_upper : Real.log 2 ≤ 0.7 := by linarith [Real.log_two_lt_d9]
  have hlogpi_lower : 1.098 < Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
        (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    linarith [Real.log_three_gt_d9]
  have hlogpi_upper : Real.log Real.pi ≤ 1.4 := by
    have hp4 :=
      Real.strictMonoOn_log.monotoneOn (show 0 < Real.pi by positivity)
        (show 0 < (4 : ℝ) by norm_num only) (le_of_lt Real.pi_lt_four)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
      norm_num only
    linarith [Real.log_two_lt_d9]
  have hcoeff :=
    Analysis.reciprocal_square_coefficient_nonneg_explicit hy hlog_upper hlog_lower
      hlog2_lower hlog2_upper hypos
  have hcompare :
    ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 ≤
      (1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1) := by
    apply (div_le_iff₀ hden).2
    have heq :
      (1 - 1 / y) ^ 2 * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) -
          ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) =
        (0.45 - Real.log 2 + Real.log Real.pi / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - Real.log Real.pi / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 := by
      field_simp
      ring
    have hpi_lower : 0 ≤ (Real.log Real.pi - 1.098) / 2 := by linarith
    have hpi_upper : 0 ≤ (1.4 - Real.log Real.pi) / (2 * y ^ 2) := by positivity
    have heq2 :
      (0.45 - Real.log 2 + Real.log Real.pi / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - Real.log Real.pi / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 =
        (0.45 - Real.log 2 + 1.098 / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - 1.4 / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 +
          (Real.log Real.pi - 1.098) / 2 +
          (1.4 - Real.log Real.pi) / (2 * y ^ 2) := by
      field_simp
      ring
    have hE :
      0 ≤
        (0.45 - Real.log 2 + Real.log Real.pi / 2) - (Real.log y + 1) / y +
          (8 * Real.log y - 11 / 4 - Real.log Real.pi / 2) / y ^ 2 +
          (-5 * Real.log y + 5 / 2) / y ^ 3 := by
      rw [heq2]
      linarith
    nlinarith only [hE, heq]
  exact hstrong.trans hcompare

/-! The c=-1 reciprocal base bound keeps the explicit odd-tail correction. -/

theorem primitiveQuadraticBRe_le_of_qneOne_neg_one_branch {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x)
    (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
          (Real.log x - 8 / 5 - (4 / 3) * Real.log 2)) /
        (1 - 1 / Real.sqrt x) ^ 2 := by
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
  have hraw :=
    primitiveQuadraticReciprocalRaw_even_le
      (show 2 ≤ χ.conductor
        by
        have hN1 : χ.conductor ≠ 1 :=
          AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprimne
        have hNpos : 0 < χ.conductor := NeZero.pos χ.conductor
        omega)
      hGRH hprimitive hprimne hinv hquad heven hx
  have hlower :=
    characterReciprocalWeightedSum_re_ge_log_sub_cneg_one x χ hquad hriemann (by linarith) hodd h2
  have hsqrt : 1 < Real.sqrt x := by
    have hxone : (1 : ℝ) < x := by linarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    nlinarith
  have hden : 0 < (1 - 1 / Real.sqrt x) ^ 2 := by
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hpos : 0 < 1 - 1 / Real.sqrt x := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hsqrtpos).2
      linarith
    positivity
  apply (le_div_iff₀ hden).2
  have hbd :
    (1 - 1 / Real.sqrt x) ^ 2 *
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2) * (1 - 1 / x) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (Real.log x - 8 / 5 - (4 / 3) * Real.log 2) := by
    linarith [hraw, hlower]
  simpa only [one_div, mul_comm, ge_iff_le] using hbd

/-!
Input/assumptions: the even quadratic c=-1 reciprocal branch at `X = y²`, `y ≥ 8`, and
`log conductor ≤ y - log 4`.
Conclusion: the reciprocal `B` bound is expressed directly in the square-radius variable.
Content: specialize the raw odd-tail estimate, normalize the square root and logarithm, and use
the nonnegative coefficient to replace the conductor logarithm by `y - log 4`.
Role: supplies the c=-1 logarithmic upper bound with this sharper conductor premise.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_neg_one_branch_at_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y - Real.log 4) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log 4 - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hx : (64 : ℝ) ≤ y ^ 2 := by nlinarith
  have hraw :=
    primitiveQuadraticBRe_le_of_qneOne_neg_one_branch χ hne hquad heven hGRH hx hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  rw [hsqrt, hlogsq] at hraw
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hy2 : 1 ≤ y ^ 2 := by nlinarith
    have hinv : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith
    linarith
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log 4 - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2) := by
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    linarith
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hraw
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum

/-!
Input/assumptions: the c=-1 reciprocal branch at `X = y²`, together with `log conductor ≤ y`.
Conclusion: the reciprocal `B` bound is expressed in the new-radius conductor scale.
Content: use the existing odd-tail raw bound and trade the conductor term directly for `y`.
Role: supplies the adapter applicable to `D = d`, before the correction comparison.
-/

theorem primitiveQuadraticBRe_le_of_qneOne_neg_one_branch_at_square_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hx : (64 : ℝ) ≤ y ^ 2 := by nlinarith
  have hraw :=
    primitiveQuadraticBRe_le_of_qneOne_neg_one_branch χ hne hquad heven hGRH hx hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  rw [hsqrt, hlogsq] at hraw
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hy2 : 1 ≤ y ^ 2 := by nlinarith
    have hinv : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith
    linarith
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2) := by
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    linarith
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hraw
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum

/-! The c=1 square specialization, retaining the same safe c=0-shaped target. -/

theorem primitiveQuadraticBRe_le_of_qneOne_one_branch_at_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| ≤
      ((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hbase :=
    primitiveQuadraticBRe_le_of_qneOne_one_branch χ hne hquad heven hGRH (by nlinarith : 64 ≤ y ^ 2)
      hriemann hodd h2
  have hsqrt : Real.sqrt (y ^ 2) = y := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hlogsq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  have hcoef : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hsq : 1 ≤ y ^ 2 := by nlinarith
    have hinv : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith
    have : 0 ≤ 1 - 1 / y ^ 2 := by linarith
    positivity
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
        (Real.log (y ^ 2) - 8 / 5 - Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2) := by
    rw [hlogsq]
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlogD (Real.log Real.pi)) hcoef
    linarith
  rw [hsqrt, hlogsq] at hbase
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  rw [hlogsq] at hnum
  calc
    _ ≤
        ((1 / 2) * (1 - 1 / y ^ 2) * (Real.log χ.conductor - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2 :=
      hbase
    _ ≤ _ := (div_le_div_iff_of_pos_right hden).2 hnum


/--
Input/assumptions: a level-`q` character with `q ≥ 3000`, `χ ≠ 1`, GRH, and a quadratic primitive
inducing character.
Conclusion: `LLSPart1PrimitiveReciprocalExplicitFormulaRawAt χ
|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|`.
Content: `y := llsTheorem11S1RadiusRoot q > 8` (`eight_lt_llsTheorem11S1RadiusRoot`) gives `x := y²
≥ 64` and
`√x = y`; `χ.primitiveCharacter.IsPrimitive` (`DirichletCharacter.primitiveCharacter_isPrimitive`)
and `χ.primitiveCharacter ≠ 1` (from `χ ≠ 1` via
`DirichletCharacter.changeLevel_primitiveCharacter`) feed `primitiveQuadraticReciprocalRaw'`
directly.
Role: connects `primitiveQuadraticReciprocalRaw'` to the Part 1 `q`-indexed API before
the reciprocal level-change correction is absorbed.
-/
theorem llsPart1PrimitiveReciprocalExplicitFormulaRawAt_of_grh_quadratic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hquad : χ.primitiveCharacter.IsQuadratic) :
    LLSPart1PrimitiveReciprocalExplicitFormulaRawAt χ
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| := by
  have hprimitive : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hprimne : χ.primitiveCharacter ≠ 1 := by
    intro hp
    have hchange := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hp] at hchange
    simp only [DirichletCharacter.changeLevel_one] at hchange
    exact hne hchange.symm
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hypos : (0 : ℝ) < llsTheorem11S1RadiusRoot q := by linarith
  have hx64 : (64 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by nlinarith
  have hsqrt : Real.sqrt ((llsTheorem11S1RadiusRoot q) ^ 2) = llsTheorem11S1RadiusRoot q := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hypos]
  have hraw :=
    primitiveQuadraticReciprocalRaw' χ.primitiveCharacter hprimitive hprimne hquad hGRH hx64
  rw [hsqrt] at hraw
  unfold LLSPart1PrimitiveReciprocalExplicitFormulaRawAt
  exact hraw


/--
Input/assumptions: LLS Lemma 2.4's Riemann reciprocal lower bound, a level-`q` character with
`q ≥ 3000`, `χ ≠ 1`, no-small-prime, GRH, and a quadratic primitive inducing character.
Conclusion: `LLSPart1PrimitiveZeroMassFullLevelRawAt χ
|PseudoPrime.AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|`.
Content: combines the analytic estimate's raw bound
(`llsPart1PrimitiveReciprocalExplicitFormulaRawAt_of_grh_quadratic`) with the established
route (b) level-change lower bound (`llsPart1PrimitiveReciprocalLowerWithLevelChangeAt_of_riemann`,
`A(q) + Δrec ≤ Re R(X,χ̃)`) and the conductor estimate's conductor absorption
(`PseudoPrime.AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption`, the generic
version, which needs no quadratic
hypothesis: `(1/2)(1-1/X)log d - Δrec ≤ (1/2)(1-1/X)log q`) via `Real.log_div` to convert both
`log(·/π)`
terms and `linarith` to chain the three inequalities.
Role: the reciprocal full-level bound in which the quotient term `Δrec` and conductor `d` have
both been eliminated in favor of the level `q`.
-/
theorem llsPart1PrimitiveZeroMassFullLevelRawAt_of_grh_quadratic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hquad : χ.primitiveCharacter.IsQuadratic) (h24 : LLSRiemannReciprocalLowerBound)
    (hsmall : llsTheorem11S1NoSmallPrime χ) :
    LLSPart1PrimitiveZeroMassFullLevelRawAt χ
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| := by
  have hraw := llsPart1PrimitiveReciprocalExplicitFormulaRawAt_of_grh_quadratic χ hq hne hGRH hquad
  unfold LLSPart1PrimitiveReciprocalExplicitFormulaRawAt at hraw
  have hlevelchange := llsPart1PrimitiveReciprocalLowerWithLevelChangeAt_of_riemann h24 χ hq hsmall
  rw [LLSPart1PrimitiveReciprocalLowerWithLevelChangeAt] at hlevelchange
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hx2 : (2 : ℝ) ≤ (llsTheorem11S1RadiusRoot q) ^ 2 := by nlinarith
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact
      ⟨χ.conductor_ne_zero, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level⟩
  have habsorb :=
    AnalyticNumberTheory.Arithmetic.primitiveReciprocalConductorAbsorption
      ((llsTheorem11S1RadiusRoot q) ^ 2) χ hx2 hqd
  have hd_ne : (χ.conductor : ℝ) ≠ 0 := by exact_mod_cast χ.conductor_ne_zero
  have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hlogd : Real.log ((χ.conductor : ℝ) / Real.pi) = Real.log χ.conductor - Real.log Real.pi :=
    Real.log_div hd_ne Real.pi_ne_zero
  have hlogq : Real.log ((q : ℝ) / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq_ne Real.pi_ne_zero
  rw [hlogd] at hraw
  unfold LLSPart1PrimitiveZeroMassFullLevelRawAt
  rw [hlogq]
  linarith [hraw, hlevelchange, habsorb]

end PseudoPrime.LLS.Extensions
