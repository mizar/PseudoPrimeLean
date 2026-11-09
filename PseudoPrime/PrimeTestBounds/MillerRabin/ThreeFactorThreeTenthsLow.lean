/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PreciseLogTaylorBounds
public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.NumberTheory.PrimeFactorLogMean
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Three-factor witnesses at small logarithmic scales -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On logarithmic scales from 8 to `52 / 5`, the exponential factor bound
is at most `3 L² / 10`. A logarithm tangent makes the normalized exponential
largest at the right endpoint, where a rational log certificate applies. -/
theorem exp_factor_le_03_low {L : ℝ} (hlo : 8 ≤ L) (hhi : L ≤ 52 / 5) :
    Real.exp (L / 3) ≤ (3 / 10 : ℝ) * L ^ 2 := by
  have hL : 0 < L := by linarith only [hlo]
  have hT : (0 : ℝ) < 52 / 5 := by norm_num only
  have hdelta : (0 : ℝ) ≤ 52 / 5 - L := by linarith only [hhi]
  have ht := Analysis.log_le_log_add_sub_div (a := L) (y := (52 / 5 : ℝ)) hL hT
  have hd :=
    div_le_div_of_nonneg_left hdelta (by norm_num only : (0 : ℝ) < 6)
      (by linarith only [hlo] : (6 : ℝ) ≤ L)
  have hc : L / 3 - 2 * Real.log L ≤ (52 / 5 : ℝ) / 3 - 2 * Real.log (52 / 5) := by
    linarith only [ht, hd]
  have he := Real.exp_le_exp.mpr hc
  have hEL : Real.exp (2 * Real.log L) = L ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hL] using (Real.exp_nat_mul (Real.log L) 2)
  have hET : Real.exp (2 * Real.log (52 / 5)) = (52 / 5 : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hT] using (Real.exp_nat_mul (Real.log (52 / 5)) 2)
  rw [Real.exp_sub, Real.exp_sub, hEL, hET] at he
  have hlog : (52 / 15 : ℝ) ≤ Real.log (4056 / 125) := by
    have hc : Analysis.preciseLogCheck (4056 / 125) 6 64 (52 / 15) 4 = true := by decide +kernel
    have h := (Analysis.preciseLogCheck_sound hc).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have hExp : Real.exp (52 / 15 : ℝ) ≤ 4056 / 125 := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by norm_num only : (0 : ℝ) < 4056 / 125)] at h
    exact h
  have hratio : Real.exp (L / 3) / L ^ 2 ≤ (4056 / 125 : ℝ) / (52 / 5) ^ 2 := by
    apply he.trans
    have heq : ((52 / 5 : ℝ) / 3) = 52 / 15 := by norm_num only
    rw [heq]
    exact div_le_div_of_nonneg_right hExp (sq_nonneg _)
  have hp := (div_le_iff₀ (sq_pos_of_pos hL)).mp hratio
  nlinarith only [hp, sq_nonneg L]

/-- Any odd input with at least three prime factors counted with multiplicity
has a rejecting prime within the 0.30 target for `8 ≤ log n ≤ 52/5`.
A prime divisor below the exponential third-scale bound is the witness. -/
theorem exists_prime_reject_03_three_low {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hlo : (8 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 52 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
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
  have hExp := exp_factor_le_03_low hlo hhi
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
