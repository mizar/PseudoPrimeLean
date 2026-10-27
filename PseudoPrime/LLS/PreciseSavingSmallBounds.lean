/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PreciseSavingTheorem11S1
public import PseudoPrime.LLS.Part1RetainedSavingSmallBounds

/-! # Finite prime caps inside the precise reciprocal-saving radius -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a modulus at least six.
Claim: the new root is at least 109/25.
Proof: retain both branches of the stronger auxiliary maximum and use the fixed log bounds.
Role: reuse prime cap nineteen without regenerating certificates. -/
theorem precise_saving_root_ge_finite_cap {q : ℕ} (hq : 6 ≤ q) :
    (109 / 25 : ℝ) ≤ preciseSavingRadiusRoot q := by
  have hl := (Analysis.rationalLogIntervalCheck_sound retained_saving_small_log_checks.1).1
  have hu := (Analysis.rationalLogIntervalCheck_sound retained_saving_small_log_checks.2.1).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl hu
  have hqlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 6) (Nat.cast_le.mpr hq)
  have hL : (17917 / 10000 : ℝ) ≤ Real.log q := hl.trans hqlog
  have huq := Real.log_le_log (by norm_num only : (0 : ℝ) < 17917 / 10000) hL
  have hlog0 : 0 < Real.log q := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hlog0 (by norm_num only : (0 : ℝ) < 2))
  rw [Real.log_div hlog0.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at ht
  have hsum := AnalyticNumberTheory.Arithmetic.primeFactorLogSum_nonneg q
  have hw : 0 ≤ 2 * (q.primeFactors.card : ℝ) * (Real.log (Real.log q)) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (sq_nonneg _))
      hlog0.le
  have hc :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log q) + 7031 / 5000 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * preciseSavingAuxiliary q)
  change _ ≤ preciseSavingCorrectionTerm q at hc
  change (109 / 25 : ℝ) ≤ Real.log q + preciseSavingCorrectionTerm q
  by_cases ha :
    0 ≤
      2 * Real.log (Real.log q) - 31551 / 20000 -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum q
  · have he :
      preciseSavingAuxiliary q =
        2 * Real.log (Real.log q) - 31551 / 20000 -
          AnalyticNumberTheory.Arithmetic.primeFactorLogSum q :=
      max_eq_right ha
    rw [he] at hc
    linarith only [hc, hw, hsum, ht, Real.log_two_lt_d9]
  · have he : preciseSavingAuxiliary q = 0 := max_eq_left (le_of_not_ge ha)
    rw [he] at hc
    linarith only [hc, hw, hu, huq, hL]

/-- Input: q >= 6. Claim: the improved squared radius is at least 19.
Proof: square the positive rational root bound. Role: reuse the finite generation catalog. -/
theorem precise_saving_radius_sq_ge_nineteen {q : ℕ} (hq : 6 ≤ q) :
    (19 : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  have hr := precise_saving_root_ge_finite_cap hq
  nlinarith only [hr, sq_nonneg (preciseSavingRadiusRoot q - 109 / 25)]

/-- Input: q >= 705. Claim: the improved squared radius is at least 43.
Proof: retain the nonnegative correction and use the certified logarithm at 705.
Role: use the same finite prime cap as for the original Part 1 formula. -/
theorem precise_saving_radius_sq_ge_forty_three {q : ℕ} (hq : 705 ≤ q) :
    (43 : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  have hl := (Analysis.rationalLogIntervalCheck_sound lls_log705_check).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hqlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 705) (Nat.cast_le.mpr hq)
  have hc : 0 ≤ preciseSavingCorrectionTerm q := le_max_left _ _
  change (43 : ℝ) ≤ (Real.log q + preciseSavingCorrectionTerm q) ^ 2
  nlinarith only [hl, hqlog, hc,
    sq_nonneg (Real.log q + preciseSavingCorrectionTerm q - 3279 / 500)]

/-- Input: 3 <= q <= 5. Claim: the refined auxiliary term vanishes.
Proof: bound log(q) by log(5) and use the nonnegative prime-support sum.
Role: control the improved correction at the smallest three moduli. -/
theorem precise_auxiliary_eq_zero_three_five {q : ℕ} (hq : 3 ≤ q) (hQ : q ≤ 5) :
    preciseSavingAuxiliary q = 0 := by
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hlog0 : 0 < Real.log q := Real.log_pos (by linarith only [hqR])
  have hqlog := Real.log_le_log (by linarith only [hqR] : (0 : ℝ) < q) (Nat.cast_le.mpr hQ)
  norm_num only [Nat.cast_ofNat] at hqlog
  have hu := (Analysis.rationalLogIntervalCheck_sound retained_saving_small_log_checks.2.2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hu
  have ht := Real.log_le_sub_one_of_pos hlog0
  apply max_eq_left
  linarith only [ht, hqlog, hu, AnalyticNumberTheory.Arithmetic.primeFactorLogSum_nonneg q]

/-- Input: 3 <= q <= 5. Claim: the improved squared radius is at least five.
Proof: keep its constant 7031/5000 and nonnegative logarithmic and local terms.
Role: certify small prime witnesses without the original larger correction. -/
theorem precise_saving_radius_sq_ge_five_three_five {q : ℕ} (hq : 3 ≤ q) (hQ : q ≤ 5) :
    (5 : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hq0 : (0 : ℝ) < q := by linarith only [hqR]
  have hL := (Real.lt_log_iff_exp_lt hq0).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hu := Real.log_nonneg hL.le
  have hw : 0 ≤ 2 * (q.primeFactors.card : ℝ) * (Real.log (Real.log q)) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (sq_nonneg _))
      (zero_lt_one.trans hL).le
  have hc :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log q) + 7031 / 5000 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * preciseSavingAuxiliary q)
  change _ ≤ preciseSavingCorrectionTerm q at hc
  rw [precise_auxiliary_eq_zero_three_five hq hQ] at hc
  change (5 : ℝ) ≤ (Real.log q + preciseSavingCorrectionTerm q) ^ 2
  nlinarith only [hc, hL, hu, hw, sq_nonneg (Real.log q + preciseSavingCorrectionTerm q - 12 / 5)]

end PseudoPrime.LLS
