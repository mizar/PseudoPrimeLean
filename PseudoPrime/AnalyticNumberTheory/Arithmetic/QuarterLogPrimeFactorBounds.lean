/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorLogDeficitBounds

/-! # A quarter-logarithm bound for distinct prime factors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The eighteen primes below 64. This fixed exception set supports a quarter-logarithm
factor-count estimate; it is independent of the input modulus. -/
def quarterPrimeExceptions : Finset ℕ :=
  {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61}

/-- A rational upper deficit at a small prime, using 69/100 as a lower bound for log two.
The dyadic exponent is p.log2. Nonnegativity is required only on the exception set. -/
def quarterPrimeDeficit (p : ℕ) : ℚ :=
  1 - (69 / 400 : ℚ) * p.log2

/-- Every exceptional rational deficit is nonnegative. Kernel-check eighteen rational
values. This permits enlarging the exceptional factors to the full fixed set. -/
theorem quarterPrimeDeficit_nonneg : ∀ p ∈ quarterPrimeExceptions, 0 ≤ quarterPrimeDeficit p := by
  decide +kernel

/-- The eighteen rational deficits sum to at most 13/2. Kernel-check the fixed sum.
This is the modulus-independent intercept in the distinct-prime estimate. -/
theorem quarterPrimeDeficit_sum_le :
    (∑ p ∈ quarterPrimeExceptions, quarterPrimeDeficit p) ≤ (13 / 2 : ℚ) := by decide +kernel

/-- At an exceptional p, a quarter of log p plus its rational deficit is at least one.
Use the dyadic lower bound on p and the certified logarithm of two. This supplies the
small-prime branch of the uniform per-prime charge. -/
theorem quarterPrimeDeficit_small {p : ℕ} (hp : p ∈ quarterPrimeExceptions) :
    (1 : ℝ) ≤ (1 / 4 : ℝ) * Real.log p + (quarterPrimeDeficit p : ℝ) := by
  have hd : ∀ p ∈ quarterPrimeExceptions, 0 < p ∧ 2 ^ p.log2 ≤ p := by decide +kernel
  have hc : ((2 ^ p.log2 : ℕ) : ℝ) ≤ p := Nat.cast_le.mpr (hd p hp).2
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hc
  have hl := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) p.log2) hc
  rw [Real.log_pow] at hl
  have hm :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg p.log2 : (0 : ℝ) ≤ p.log2)
  dsimp only [quarterPrimeDeficit]
  norm_num only [Rat.cast_sub, Rat.cast_one, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_natCast]
  nlinarith only [hl, hm, Nat.cast_nonneg (α := ℝ) p.log2]

/-- Every prime is charged by a quarter of its logarithm and its exceptional deficit.
Primes outside the exception set are at least 64. This supplies the generic deficit theorem. -/
theorem quarterPrimeDeficit_prime {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤
      (1 / 4 : ℝ) * Real.log p +
        if p ∈ quarterPrimeExceptions then (quarterPrimeDeficit p : ℝ) else 0 := by
  by_cases hs : p ∈ quarterPrimeExceptions
  · rw [ite_eq_left hs]
    exact quarterPrimeDeficit_small hs
  · rw [ite_eq_right hs, add_zero]
    have hall : ∀ p ∈ Finset.range 64, p.Prime → p ∈ quarterPrimeExceptions := by decide +kernel
    have hbig : 64 ≤ p := by
      by_contra h
      exact hs (hall p (Finset.mem_range.mpr (lt_of_not_ge h)) hp)
    have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 64) (Nat.cast_le.mpr hbig)
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl, Real.log_two_gt_d9]

/-- For positive q at most A, the number of distinct prime factors is at most
13/2+(1/4)log A. Sum the per-prime charges and the eighteen fixed deficits.
No RH, parity, or finite input-range certificate is required. This sharpens local witness costs. -/
theorem primeFactors_card_le_thirteen_halves_add_quarter_log {q A : ℕ} (hq : 0 < q) (hqA : q ≤ A) :
    (q.primeFactors.card : ℝ) ≤ 13 / 2 + (1 / 4 : ℝ) * Real.log A := by
  have h :=
    primeFactors_card_le_log_deficit hq hqA (by norm_num only : (0 : ℝ) ≤ 1 / 4)
      quarterPrimeExceptions (fun p ↦ (quarterPrimeDeficit p : ℝ))
      (fun p hp ↦ Rat.cast_nonneg.mpr (quarterPrimeDeficit_nonneg p hp))
      (fun p hp ↦ quarterPrimeDeficit_prime hp)
  have hs : (∑ p ∈ quarterPrimeExceptions, (quarterPrimeDeficit p : ℝ)) ≤ 13 / 2 := by
    rw [← Rat.cast_sum]
    have hh := (Rat.cast_le (K := ℝ)).mpr quarterPrimeDeficit_sum_le
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh
  linarith only [h, hs]

/-- Above logarithmic level 32, the quarter-logarithm affine budget is strictly smaller
than the earlier 5/2+(3/8)L budget. Rearrange a rational linear inequality.
This identifies the range where the new local-cost estimate improves the old one. -/
theorem quarter_factor_budget_lt_old {L : ℝ} (hL : 32 < L) :
    13 / 2 + (1 / 4 : ℝ) * L < 5 / 2 + (3 / 8 : ℝ) * L := by linarith only [hL]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
