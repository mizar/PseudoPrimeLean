/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePowerCountingCriteria

/-! # Analytic prime supplies for repeated-product counting -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check a prime supply at the square cutoff `b²`. The input `v` specifies relative width
`1/v`, while `j`, `n`, `lo` and `hi` describe a rational Taylor interval for `log (b²)`.
The remaining rational inequality checks the budget required by the RH prime-count bound.
The soundness theorem permits each checked supply to be reused at any product degree. -/
def rhSupplyCheck (b M v j n : ℕ) (lo hi : ℚ) : Bool :=
  decide
    (1 < b ∧
      2 ≤ v ∧
      (M : ℚ) * hi ≤ (1 - 1 / v) * (b : ℚ) ^ 2 - ((b : ℚ) / 10 + 21 / 10) * v - 1839 / 1000 ∧
      Analysis.rationalLogIntervalCheck (b ^ 2 : ℕ) j n lo hi = true)

/-- Under RH, a successful rational supply check gives at least `M` primes up to `b²`.
The proof transfers the Taylor and budget certificates to the reals, evaluates the square
root, and applies the existing relative Chebyshev prime-count bound. -/
theorem rhSupplyCheck_sound (hRH : RiemannHypothesis) {b M v j n : ℕ} {lo hi : ℚ}
    (h : rhSupplyCheck b M v j n lo hi = true) : M ≤ (b ^ 2).primeCounting := by
  have hr :
    1 < b ∧
      2 ≤ v ∧
      (M : ℚ) * hi ≤ (1 - 1 / v) * (b : ℚ) ^ 2 - ((b : ℚ) / 10 + 21 / 10) * v - 1839 / 1000 ∧
      Analysis.rationalLogIntervalCheck (b ^ 2 : ℕ) j n lo hi = true :=
    of_decide_eq_true h
  have hl := (Analysis.rationalLogIntervalCheck_sound hr.2.2.2).2
  have hl' : Real.log ((b : ℝ) ^ 2) ≤ (hi : ℝ) := by
    simpa only [Rat.cast_natCast, Rat.cast_pow, Nat.cast_pow] using hl
  have hv : (2 : ℝ) ≤ v := by exact_mod_cast hr.2.1
  have hvpos : (0 : ℝ) < v := by linarith only [hv]
  have hh : (0 : ℝ) < 1 / v := one_div_pos.mpr hvpos
  have hh1 : (1 : ℝ) / v ≤ 1 / 2 := by exact one_div_le_one_div_of_le (by norm_num only) hv
  have hsqrt : Real.sqrt ((b : ℝ) ^ 2) = b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg b)]
  have hbudget :
    (M : ℝ) * (hi : ℝ) ≤
      (1 - 1 / v) * (b : ℝ) ^ 2 - ((b : ℝ) / 10 + 21 / 10) * v - 1839 / 1000 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hr.2.2.1
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_natCast] using hc
  apply primeCount_ge_of_relative_psi hRH hh hh1 (B := b ^ 2) (M := M) (by nlinarith only [hr.1])
  rw [Nat.cast_pow, hsqrt]
  have hmul := mul_le_mul_of_nonneg_left hl' (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  rw [one_div, div_inv_eq_mul]
  rw [one_div] at hbudget
  linarith only [hmul, hbudget]

/-- Parameters for an RH prime supply at the square cutoff `root²`. The fields record the
required prime count, reciprocal relative width, binary logarithm scale and rational logarithm
upper endpoint. These data are checked once and reused for different product degrees. -/
structure AnalyticPrimeSupply where
  /-- Square root of the prime cutoff. -/
  root : ℕ
  /-- Required lower bound on the number of primes. -/
  count : ℕ
  /-- Reciprocal relative width in the Chebyshev estimate. -/
  width : ℕ
  /-- Binary scale for the logarithm certificate. -/
  scale : ℕ
  /-- Rational upper bound for the logarithm of the cutoff. -/
  upper : ℚ

/-- Check a supply using 32 Taylor terms and zero as a lower logarithm endpoint. The checker
also verifies the upper endpoint and all hypotheses required by the prime-count bound. -/
def AnalyticPrimeSupply.check (c : AnalyticPrimeSupply) : Bool :=
  rhSupplyCheck c.root c.count c.width c.scale 32 0 c.upper

/-- Under RH, a checked supply yields its stated lower bound on the number of primes. This
specializes the general rational checker to the fixed Taylor length used by the supply table. -/
theorem AnalyticPrimeSupply.sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (h : c.check = true) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact rhSupplyCheck_sound hRH h

end PseudoPrime.PrimeTestBounds.MillerRabin
