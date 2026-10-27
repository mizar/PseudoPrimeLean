/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCertificates

/-! # Integer prime caps below the original Part 2 log-square cutoff -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a positive left endpoint a <= q, a checked rational log interval,
a nonnegative lower endpoint lo and cap <= lo^2.
Claim: cap <= (log q)^2. Proof: use monotonicity of log and a square comparison.
Role: keep all finite certificate checks independent of real logarithm evaluation. -/
theorem log_sq_ge_of_rational_check {a q cap j k : ℕ} {lo hi : ℚ} (ha : 0 < a) (haq : a ≤ q)
    (hc : Analysis.rationalLogIntervalCheck (a : ℚ) j k lo hi = true) (hlo : (0 : ℝ) ≤ (lo : ℝ))
    (hcap : (cap : ℝ) ≤ (lo : ℝ) ^ 2) : (cap : ℝ) ≤ (Real.log q) ^ 2 := by
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_natCast] at hl
  have hq := Real.log_le_log (Nat.cast_pos.mpr ha) (Nat.cast_le.mpr haq)
  nlinarith only [hl, hq, hlo, hcap, sq_nonneg (Real.log q - (lo : ℝ))]

/-- Input: none. Claim: certified rational intervals enclose logs of 5, 7, 11, 17 and 79.
Proof: check the finite Taylor arithmetic in the kernel.
Role: place prime caps 2, 3, 5, 7 and 19 below the original Part 2 cutoff. -/
theorem part2_small_log_checks :
    Analysis.rationalLogIntervalCheck 5 3 20 (3 / 2) 2 = true ∧
      Analysis.rationalLogIntervalCheck 7 3 20 (7 / 4) 2 = true ∧
      Analysis.rationalLogIntervalCheck 11 4 20 (9 / 4) 3 = true ∧
      Analysis.rationalLogIntervalCheck 17 5 20 (8 / 3) 3 = true ∧
      Analysis.rationalLogIntervalCheck 79 7 20 (109 / 25) 5 = true := by
  decide +kernel

/-- Input: a natural modulus q.
Output: cap 2 below 7, cap 3 below 11, cap 5 below 17 and cap 7 thereafter.
Role: match small prime-divisor or group-generation certificates to log squared. -/
def part2SmallPrimeCap (q : ℕ) : ℕ :=
  if q < 7 then 2 else if q < 11 then 3 else if q < 17 then 5 else 7

/-- Input: q >= 5. Claim: the selected small prime cap is at most (log q)^2.
Proof: split the four cap intervals and use their checked logarithm lower bounds.
Role: transfer the small exact certificates to the original Part 2 formula. -/
theorem part2_small_cap_le_log_sq {q : ℕ} (hq : 5 ≤ q) :
    (part2SmallPrimeCap q : ℝ) ≤ (Real.log q) ^ 2 := by
  by_cases h7 : q < 7
  · simpa only [part2SmallPrimeCap, ite_eq_left h7, Nat.cast_ofNat] using
      log_sq_ge_of_rational_check (cap := 2) (by decide +kernel : 0 < 5) hq part2_small_log_checks.1
        (by norm_num only) (by norm_num only)
  · by_cases h11 : q < 11
    · simpa only [part2SmallPrimeCap, ite_eq_right h7, ite_eq_left h11, Nat.cast_ofNat] using
        log_sq_ge_of_rational_check (cap := 3) (by decide +kernel : 0 < 7) (Nat.le_of_not_gt h7)
          part2_small_log_checks.2.1 (by norm_num only) (by norm_num only)
    · by_cases h17 : q < 17
      · simpa only [part2SmallPrimeCap, ite_eq_right h7, ite_eq_right h11, ite_eq_left h17,
          Nat.cast_ofNat] using
          log_sq_ge_of_rational_check (cap := 5) (by decide +kernel : 0 < 11) (Nat.le_of_not_gt h11)
            part2_small_log_checks.2.2.1 (by norm_num only) (by norm_num only)
      · simpa only [part2SmallPrimeCap, ite_eq_right h7, ite_eq_right h11, ite_eq_right h17,
          Nat.cast_ofNat] using
          log_sq_ge_of_rational_check (cap := 7) (by decide +kernel : 0 < 17) (Nat.le_of_not_gt h17)
            part2_small_log_checks.2.2.2.1 (by norm_num only) (by norm_num only)

/-- Input: q >= 79. Claim: the existing Part 1 catalog cap is at most (log q)^2.
Proof: split at 705 and use the checked logarithms at 79 and 705.
Role: reuse the complete catalog without introducing new group-generation data. -/
theorem part2_catalog_cap_le_log_sq {q : ℕ} (hq : 79 ≤ q) :
    (llsPart1FinitePrimeCap q : ℝ) ≤ (Real.log q) ^ 2 := by
  by_cases h : q < 705
  · simpa only [llsPart1FinitePrimeCap, ite_eq_left h, Nat.cast_ofNat] using
      log_sq_ge_of_rational_check (cap := 19) (by decide +kernel : 0 < 79) hq
        part2_small_log_checks.2.2.2.2 (by norm_num only) (by norm_num only)
  · simpa only [llsPart1FinitePrimeCap, ite_eq_right h, Nat.cast_ofNat] using
      log_sq_ge_of_rational_check (cap := 43) (by decide +kernel : 0 < 705) (Nat.le_of_not_gt h)
        lls_log705_check (by norm_num only) (by norm_num only)

end PseudoPrime.LLS
