/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LowExponential4136
public import PseudoPrime.NumberTheory.PrimeFactorLogMean
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Low-range three-factor witness from a prime divisor -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input with at least three prime factors and logarithm in `[8, 25/2]` has a
rejecting prime at most `(517/1250) * (log n)²`. The logarithmic mean of two factors
shows that one factor is at most `exp (log n / 3)`; that factor itself rejects. -/
theorem exists_prime_reject_three_factors_low {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hlo : (8 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 25 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (517 / 1250 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hk2 : 2 ≤ n.primeFactorsList.length := by
    change 2 ≤ ArithmeticFunction.cardFactors n
    exact le_trans (by norm_num only) hk
  obtain ⟨p, q, hp, hq, hd, hm⟩ :=
    NumberTheory.exists_prime_pair_log_mean (Nat.zero_lt_of_lt hn) hk2
  have hkR : (3 : ℝ) ≤ ArithmeticFunction.cardFactors n := Nat.cast_le.mpr hk
  have hkpos : (0 : ℝ) < ArithmeticFunction.cardFactors n := by linarith only [hkR]
  have hlog :
    Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) := by
    apply (le_div_iff₀ hkpos).mpr
    simpa only [ArithmeticFunction.cardFactors_apply, mul_comm] using hm
  have hL : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
  have hratio : 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) ≤ 2 * Real.log n / 3 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num only) hL) (by norm_num only) hkR
  have hsum : Real.log p + Real.log q ≤ 2 * Real.log n / 3 := by
    have h := hlog.trans hratio
    rw [Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)] at h
    exact h
  have hpn : p ∣ n := (dvd_mul_right p q).trans hd
  have hqn : q ∣ n := (dvd_mul_left q p).trans hd
  have hExp := exp_factor_le_4136 hlo hhi
  by_cases hle : Real.log p ≤ Real.log q
  · have hpLog : Real.log p ≤ Real.log n / 3 := by linarith only [hsum, hle]
    exact
      ⟨p, hp, (Real.le_exp_of_log_le hpLog).trans hExp,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · have hqLog : Real.log q ≤ Real.log n / 3 := by linarith only [hsum, le_of_not_ge hle]
    exact
      ⟨q, hq, (Real.le_exp_of_log_le hqLog).trans hExp,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hq hqn⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
