/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EightSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028NextInterval

/-! # Further low interval for coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime below 23 is at most 19. Exact primality checks rule out the
three intervening integers. -/
theorem target028_prime_le19 {p : ℕ} (hp : p.Prime) (h : (p : ℝ) < 23) : p ≤ 19 := by
  have h23 : p < 23 := by exact_mod_cast h
  by_contra hn
  have hnp : ∀ k ∈ Finset.Icc 20 22, ¬Nat.Prime k := by decide +kernel
  have hlo : 20 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hhi : p ≤ 22 := Nat.le_of_lt_succ h23
  exact hnp p (Finset.mem_Icc.mpr ⟨hlo, hhi⟩) hp

/-- Any odd input with at least three prime factors counted with multiplicity
has a rejecting prime within the 0.28 target for `8.83 ≤ log n ≤ 9.4`.
A prime divisor below the exponential third-scale bound is the witness. -/
theorem exists_prime_reject_028_three_extended {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hlo : (883 / 100 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 47 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
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
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 23 5 32 (627 / 200) 4 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hExp : Real.exp (Real.log n / 3) < 23 := by
    have h :=
      Real.exp_lt_exp.mpr (show Real.log n / 3 < Real.log (23 : ℝ) by linarith only [hhi, hcert])
    simpa only [Real.exp_log (by norm_num only : (0 : ℝ) < 23)] using h
  have hbound : (19 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hlo]
  by_cases hle : Real.log p ≤ Real.log q
  · have hpLog : Real.log p ≤ Real.log n / 3 := by linarith only [hsum, hle]
    exact
      ⟨p, hp,
        (Nat.cast_le.mpr
              (target028_prime_le19 hp ((Real.le_exp_of_log_le hpLog).trans_lt hExp))).trans
          hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · have hqLog : Real.log q ≤ Real.log n / 3 := by linarith only [hsum, le_of_not_ge hle]
    exact
      ⟨q, hq,
        (Nat.cast_le.mpr
              (target028_prime_le19 hq ((Real.le_exp_of_log_le hqLog).trans_lt hExp))).trans
          hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hq hqn⟩

/-- Under GRH, every odd composite whose logarithm lies between 8 and 9.4
has a 0.28 rejecting prime. The earlier interval and the square, factor-count,
and four adjacent semiprime branches cover all possibilities. -/
theorem exists_prime_reject_028_through94 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 47 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hfirst : Real.log n ≤ 883 / 100
  · exact exists_prime_reject_028_through883 hn ho hc hGRH hL hfirst
  have h883 : (883 / 100 : ℝ) ≤ Real.log n := le_of_not_ge hfirst
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_028_square_through97 hn ho hp hd hL (by linarith only [hU])
  by_cases hk : 3 ≤ ArithmeticFunction.cardFactors n
  · exact exists_prime_reject_028_three_extended hn ho hk h883 hU
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  have hkeq : ArithmeticFunction.cardFactors n = 2 :=
    Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hk)) hk2
  obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
    NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hkeq
  rcases hpq.eq_or_lt with heq | hlt
  · subst q
    exact False.elim (hsq ⟨p, hp, by rw [hprod, pow_two]⟩)
  by_cases h1 : Real.log n ≤ 179 / 20
  · exact target028_eight_cell46 hn ho hp hq hlt hprod hGRH h883 h1
  by_cases h2 : Real.log n ≤ 91 / 10
  · exact target028_eight_cell47 hn ho hp hq hlt hprod hGRH (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ 233 / 25
  · exact target028_eight_cell48 hn ho hp hq hlt hprod hGRH (le_of_not_ge h2) h3
  · exact
      target028_eight_cell49 hn ho hp hq hlt hprod hGRH (le_of_not_ge h3) (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin
