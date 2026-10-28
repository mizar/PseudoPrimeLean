/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Statement
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.Part1SmallRadiusBounds

/-! # Uniform finite caps for the original LLS Part 1 radius -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: q >= 4. Claim: the original LLS Part 1 radius root is at least 219/50.
Proof: split the auxiliary maximum and retain the nonnegative local loss.
Use log(t/2) <= t/2-1 to bound the positive auxiliary branch.
Role: transfer a uniform finite prime cap to the exact original formula. -/
theorem lls_part1_root_ge_small_cap {q : ℕ} (hq : 4 ≤ q) :
    (219 / 50 : ℝ) ≤ Real.log q + llsCorrectionTerm q := by
  have hqR : (4 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hq0 : (0 : ℝ) < q := by linarith only [hqR]
  have hL :=
    (Real.lt_log_iff_exp_lt hq0).mpr
      (Real.exp_one_lt_three.trans_le (by linarith only [hqR] : (3 : ℝ) ≤ q))
  have h4 := Real.log_le_log (by norm_num only : (0 : ℝ) < 4) hqR
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow] at h4
  norm_num only [Nat.cast_ofNat] at h4
  have hu := Real.log_nonneg hL.le
  have ht :=
    Real.log_le_sub_one_of_pos (div_pos (zero_lt_one.trans hL) (by norm_num only : (0 : ℝ) < 2))
  rw [Real.log_div (ne_of_gt (zero_lt_one.trans hL)) (by norm_num only : (2 : ℝ) ≠ 0)] at ht
  have hsum := AnalyticNumberTheory.Arithmetic.primeFactorLogSum_nonneg q
  have hw : 0 ≤ 2 * (q.primeFactors.card : ℝ) * (Real.log (Real.log q)) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (sq_nonneg _))
      (zero_lt_one.trans hL).le
  have hc :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log q) + 3 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * llsAuxiliaryTerm q)
  change _ ≤ llsCorrectionTerm q at hc
  by_cases ha :
    0 ≤ 2 * Real.log (Real.log q) - 8 / 5 - AnalyticNumberTheory.Arithmetic.primeFactorLogSum q
  · have he :
      llsAuxiliaryTerm q =
        2 * Real.log (Real.log q) - 8 / 5 - AnalyticNumberTheory.Arithmetic.primeFactorLogSum q :=
      max_eq_right ha
    rw [he] at hc
    linarith only [hc, hw, hsum, ht, Real.log_two_lt_d9]
  · have he : llsAuxiliaryTerm q = 0 := max_eq_left (le_of_not_ge ha)
    rw [he] at hc
    linarith only [hc, hw, hu, h4, Real.log_two_gt_d9]

/-- Input: q >= 4. Claim: the original Part 1 squared radius is at least 19.
Proof: square the positive lower root bound. Role: cover small-modulus generation caps. -/
theorem lls_part1_radius_sq_ge_nineteen {q : ℕ} (hq : 4 ≤ q) :
    (19 : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  have h := lls_part1_root_ge_small_cap hq
  nlinarith only [h, sq_nonneg (Real.log q + llsCorrectionTerm q - 219 / 50)]

/-- Claim: a rational Taylor interval gives log(705) >= 3279/500.
Proof: exact kernel arithmetic. Role: compare the larger finite cap with the squared logarithm. -/
theorem lls_log705_check : Analysis.rationalLogIntervalCheck 705 10 20 (3279 / 500) 7 = true := by
  decide +kernel

/-- Input: q >= 705. Claim: the original Part 1 squared radius is at least 43.
Proof: retain its nonnegative correction and use the certified logarithm at 705.
Role: accommodate the finite prime cap through modulus 2999. -/
theorem lls_part1_radius_sq_ge_forty_three {q : ℕ} (hq : 705 ≤ q) :
    (43 : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  have hl := (Analysis.rationalLogIntervalCheck_sound lls_log705_check).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 705) (Nat.cast_le.mpr hq)
  have hc := llsCorrectionTerm_nonneg q
  nlinarith only [hl, hlog, hc, sq_nonneg (Real.log q + llsCorrectionTerm q - 3279 / 500)]

/-- Input: 3 <= q <= 4. Claim: 1 < log(q) < 7/5.
Proof: compare exp(1) with three and log(q) with twice log(2).
Role: control both small auxiliary terms. -/
theorem log_level_bounds_three_four {q : ℕ} (hq : 3 ≤ q) (hQ : q ≤ 4) :
    1 < Real.log q ∧ Real.log q < 7 / 5 := by
  have hqR : (3 : ℝ) ≤ q := Nat.cast_le.mpr hq
  have hQ_R : (q : ℝ) ≤ 4 := Nat.cast_le.mpr hQ
  have hq0 : (0 : ℝ) < q := by linarith only [hqR]
  have hl := (Real.lt_log_iff_exp_lt hq0).mpr (Real.exp_one_lt_three.trans_le hqR)
  have hu := Real.log_le_log hq0 hQ_R
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  exact ⟨hl, by linarith only [hu, Real.log_two_lt_d9]⟩

/-- Input: 3 <= q <= 4. Claim: the original LLS auxiliary term vanishes.
Proof: combine log(t) <= t-1 with the nonnegative prime-support sum.
Role: identify the exact small-modulus correction. -/
theorem llsAuxiliaryTerm_eq_zero_three_four {q : ℕ} (hq : 3 ≤ q) (hQ : q ≤ 4) :
    llsAuxiliaryTerm q = 0 := by
  have hL := log_level_bounds_three_four hq hQ
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans hL.1)
  apply max_eq_left
  linarith only [hl, hL.2, AnalyticNumberTheory.Arithmetic.primeFactorLogSum_nonneg q]

/-- Input: 3 <= q <= 4. Claim: the original LLS correction is at least three.
Proof: use the vanishing auxiliary term and retain the other nonnegative terms.
Role: bound the original radius without numerical logarithm approximations. -/
theorem llsCorrectionTerm_ge_three_three_four {q : ℕ} (hq : 3 ≤ q) (hQ : q ≤ 4) :
    (3 : ℝ) ≤ llsCorrectionTerm q := by
  have hL := log_level_bounds_three_four hq hQ
  have hu := Real.log_nonneg hL.1.le
  have hw : 0 ≤ 2 * (q.primeFactors.card : ℝ) * (Real.log (Real.log q)) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (sq_nonneg _))
      (zero_lt_one.trans hL.1).le
  have h :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log q) + 3 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * llsAuxiliaryTerm q)
  rw [llsAuxiliaryTerm_eq_zero_three_four hq hQ] at h
  change (3 : ℝ) ≤ max 0 _
  rw [llsAuxiliaryTerm_eq_zero_three_four hq hQ]
  linarith only [h, hu, hw]

/-- Input: 3 <= q <= 4. Claim: the original Part 1 squared radius is at least 16.
Proof: its positive root exceeds four. Role: contain the finite witnesses two and three. -/
theorem lls_part1_radius_sq_ge_sixteen_three_four {q : ℕ} (hq : 3 ≤ q) (hQ : q ≤ 4) :
    (16 : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  have hl := (log_level_bounds_three_four hq hQ).1
  have hc := llsCorrectionTerm_ge_three_three_four hq hQ
  nlinarith only [hl, hc, sq_nonneg (Real.log q + llsCorrectionTerm q - 4)]

end PseudoPrime.LLS
