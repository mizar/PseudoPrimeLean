/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64RamifiedIntervalCertificate

/-! # Rational ramified-cost certificates up to scale 1700 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Rounded upper local costs for scales from 1600 to 1700.
The finite checks below validate the rational Euler and Taylor allowances.
These data reuse the ratio intervals and power counts of the original certificate. -/
def phase64LocalCostUpper1700 (p : ℕ) : ℚ :=
  (match p with
      | 3 => 575071
      | 5 => 289004
      | 7 => 194811
      | 11 => 121850
      | 13 => 103397
      | 17 => 79300
      | 19 => 73467
      | 23 => 64656
      | 29 => 55330
      | 31 => 52832
      | 37 => 46521
      | 41 => 43075
      | 43 => 41541
      | 47 => 38808
      | 53 => 35454
      | 59 => 32865
      | 61 => 32148
      | 67 => 28585
      | 71 => 28155
      | 73 => 27958
      | 79 => 27431
      | 83 => 27122
      | 89 => 26712
      | 97 => 26241
      | _ => 0 :
      ℕ) /
    1000000

/-- Exact kernel check 0: the rational allowances satisfy the stated bound.
The aggregate check retains the existing 13/5 budget; local checks verify the
cutoff and Taylor prefix at upper scale 1700 for each retained prime. -/
theorem phase64_local_1700_check0 :
    (phase64LocalPrimes.map
          (fun p ↦ phase64LocalLogUpper p * max (phase64LocalCostUpper1700 p - 3 / 100) 0)).sum ≤
      (13 / 5 : ℚ) := by
  decide +kernel

/-- Exact kernel check 1: the rational allowances satisfy the stated bound.
The aggregate check retains the existing 13/5 budget; local checks verify the
cutoff and Taylor prefix at upper scale 1700 for each retained prime. -/
theorem phase64_local_1700_check1 :
    ([3, 5, 7, 11, 13, 17, 19, 23] : List ℕ).Forall
      (fun (p : ℕ) ↦
        (99 / 40 : ℚ) * 1700 ≤ (p : ℚ) ^ (phase64LocalPowerCount p + 1) ∧
          phase64LocalEulerUpper p + primeExpPrefixUpper p 1700 (phase64LocalPowerCount p) / 40 ≤
            phase64LocalCostUpper1700 p) := by
  decide +kernel

/-- Exact kernel check 2: the rational allowances satisfy the stated bound.
The aggregate check retains the existing 13/5 budget; local checks verify the
cutoff and Taylor prefix at upper scale 1700 for each retained prime. -/
theorem phase64_local_1700_check2 :
    ([29, 31, 37, 41, 43, 47, 53, 59] : List ℕ).Forall
      (fun (p : ℕ) ↦
        (99 / 40 : ℚ) * 1700 ≤ (p : ℚ) ^ (phase64LocalPowerCount p + 1) ∧
          phase64LocalEulerUpper p + primeExpPrefixUpper p 1700 (phase64LocalPowerCount p) / 40 ≤
            phase64LocalCostUpper1700 p) := by
  decide +kernel

/-- Exact kernel check 3: the rational allowances satisfy the stated bound.
The aggregate check retains the existing 13/5 budget; local checks verify the
cutoff and Taylor prefix at upper scale 1700 for each retained prime. -/
theorem phase64_local_1700_check3 :
    ([61, 67, 71, 73, 79, 83, 89, 97] : List ℕ).Forall
      (fun (p : ℕ) ↦
        (99 / 40 : ℚ) * 1700 ≤ (p : ℚ) ^ (phase64LocalPowerCount p + 1) ∧
          phase64LocalEulerUpper p + primeExpPrefixUpper p 1700 (phase64LocalPowerCount p) / 40 ≤
            phase64LocalCostUpper1700 p) := by
  decide +kernel

end PseudoPrime.Analysis
