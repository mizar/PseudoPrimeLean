/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeCount
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Largest analytic four-ninths certificate cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The twelve-term rational checker bounds the logarithm of the largest
analytic radius. Its upper bound supplies both the size and prime-count
conditions for the last square cell. -/
theorem fourNinths_maxCell_log : Real.log (428403 : ℝ) ≤ 12967819625231 / 1000000000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck 428403 19 12 (12967819615103 / 1000000000000)
        (12967819625231 / 1000000000000) =
      true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Under RH the largest analytic radius contains at least 32205 primes.
The certified logarithm and a rational square-root bound verify the relative
psi supply at width `13 / 1000`; no prime enumeration is used. -/
theorem fourNinths_maxCell_primeCount (hRH : RiemannHypothesis) :
    32205 ≤ (428403 : ℕ).primeCounting := by
  have hs : Real.sqrt (428403 : ℝ) ≤ 655 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num only
    · norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := (13 / 1000 : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [fourNinths_maxCell_log, hs]

/-- The largest cell's binomial coefficient exceeds a compact integer lower
bound. Compare the 78-factor descending factorial with 78! times this bound;
the proof avoids expanding the factorial of 32205. -/
theorem fourNinths_maxCell_choose : 333 * 10 ^ 234 ≤ Nat.choose 32205 78 := by
  apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 78)
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
    Nat.mul_zero, Nat.add_zero]

/-- The upper endpoint of the largest square cell is below twice the logarithm
of its binomial count. Use the compact integer lower bound and two small
twelve-term logarithm checks instead of a 237-digit logarithm input. -/
theorem fourNinths_maxCell_count_log :
    (54461 / 50 : ℝ) < 2 * Real.log (Nat.choose 32205 78 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck 333 8 12 (5808 / 1000) 6 = true := by decide +kernel
  have hd : Analysis.rationalLogIntervalCheck 10 3 12 (2302585 / 1000000) 3 = true := by
    decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).1
  have ht := (Analysis.rationalLogIntervalCheck_sound hd).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl ht
  have hle : Real.log ((333 : ℝ) * 10 ^ 234) ≤ Real.log (Nat.choose 32205 78 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast fourNinths_maxCell_choose
  rw [Real.log_mul (by norm_num only : (333 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  linarith only [hl, ht, hle]

/-- The radius and product size satisfy the scalar conditions at the lower
endpoint of the largest square cell. Combine the certified logarithm with
exact rational arithmetic. -/
theorem fourNinths_maxCell_size :
    (9 : ℝ) * 428403 ≤ 4 * (101149 / 100 : ℝ) ^ 2 ∧ 78 * Real.log 428403 < 101149 / 100 := by
  constructor
  · norm_num only
  · linarith only [fourNinths_maxCell_log]

end PseudoPrime.PrimeTestBounds.MillerRabin
