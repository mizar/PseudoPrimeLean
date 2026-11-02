/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SmallPrimeLogTail
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # The selected small-prime constant at cutoff thirty-one

Eleven rational logarithm certificates bound the finite excess constant used by the
precise-saving root. These fixed numerical choices stay outside the general arbitrary
cutoff theorem. No interval of Jacobi inputs is enumerated. Keep endpoint-window
certificates separate so their later adjustment does not rebuild this root provider.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The logarithm of 2 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log2_le : Real.log (2 : ℝ) ≤ (173287 / 250000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 2 1 20 (693147 / 1000000) (173287 / 250000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 3 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log3_le : Real.log (3 : ℝ) ≤ (1098613 / 1000000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 3 2 20 (274653 / 250000) (1098613 / 1000000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 5 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log5_le : Real.log (5 : ℝ) ≤ (804719 / 500000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 5 2 20 (1609437 / 1000000) (804719 / 500000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 7 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log7_le : Real.log (7 : ℝ) ≤ (1945911 / 1000000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 7 3 20 (194591 / 100000) (1945911 / 1000000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 11 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log11_le : Real.log (11 : ℝ) ≤ (299737 / 125000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 11 3 20 (479579 / 200000) (299737 / 125000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 13 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log13_le : Real.log (13 : ℝ) ≤ (51299 / 20000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 13 4 20 (2564949 / 1000000) (51299 / 20000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 17 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log17_le : Real.log (17 : ℝ) ≤ (1416607 / 500000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 17 4 20 (2833213 / 1000000) (1416607 / 500000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 19 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log19_le : Real.log (19 : ℝ) ≤ (2944439 / 1000000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 19 4 20 (1472219 / 500000) (2944439 / 1000000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 23 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log23_le : Real.log (23 : ℝ) ≤ (627099 / 200000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 23 5 20 (1567747 / 500000) (627099 / 200000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 29 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log29_le : Real.log (29 : ℝ) ≤ (52614 / 15625 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck 29 5 20 (673459 / 200000) (52614 / 15625) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The logarithm of 31 is below its selected rational upper endpoint.
Input: none. Claim: the fixed logarithm bound. Proof: a twenty-term rational certificate.
Role: one of the eleven weighted contributions to the cutoff-thirty-one constant. -/
private theorem prime31_log31_le : Real.log (31 : ℝ) ≤ (858497 / 250000 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck 31 5 20 (3433987 / 1000000) (858497 / 250000) = true := by
    decide +kernel
  have hb := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact hb

/-- The selected cutoff-thirty-one excess constant is strictly below 2.3011.
Input: none. Claim: the complete small-prime contribution has the stated rational cap.
Proof: identify the eleven primes and combine their certified logarithms with positive weights.
Role: close the precise-saving root majorant without a large finite-input computation. -/
theorem prime31_log_constant_lt : NumberTheory.smallPrimeLogConstant 31 < (23011 / 10000 : ℝ) := by
  have hp :
    (Finset.range (31 + 1)).filter Nat.Prime = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
    decide +kernel
  dsimp only [NumberTheory.smallPrimeLogConstant]
  rw [hp]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Nat.reduceEqDiff, false_or, not_false_eq_true, NumberTheory.primeLogTailWeight]
  norm_num only
  linarith only [prime31_log2_le, prime31_log3_le, prime31_log5_le, prime31_log7_le,
    prime31_log11_le, prime31_log13_le, prime31_log17_le, prime31_log19_le, prime31_log23_le,
    prime31_log29_le, prime31_log31_le]

end PseudoPrime.LLS
