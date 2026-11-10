/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.NumberTheory.PrimeFactorPairClassification
public import PseudoPrime.NumberTheory.PrimeFactorLogMean

/-! # Three-factor first interval for coefficient one quarter -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Any odd input with at least three prime factors counted with multiplicity
has a rejecting prime within the quarter-square target for `8 ≤ log n ≤ 9.4`.
A prime divisor below the exponential third-scale bound is the witness. -/
theorem exists_prime_reject_quarter_three_first {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hlo : (8 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 47 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
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
  have hsmall : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ Real.log r ≤ Real.log n / 3 := by
    by_cases hle : Real.log p ≤ Real.log q
    · exact ⟨p, hp, hpn, by linarith only [hsum, hle]⟩
    · exact ⟨q, hq, hqn, by linarith only [hsum, le_of_not_ge hle]⟩
  obtain ⟨r, hr, hrd, hrlog⟩ := hsmall
  have hrexp := Real.le_exp_of_log_le hrlog
  by_cases hsplit : Real.log n ≤ 83 / 10
  · have hcert :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 16 4 32 (83 / 30) 3 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
    have hExp : Real.exp (Real.log n / 3) ≤ 16 := by
      have h :=
        Real.exp_le_exp.mpr
          (show Real.log n / 3 ≤ Real.log (16 : ℝ) by linarith only [hsplit, hcert])
      simpa only [Real.exp_log (by norm_num only : (0 : ℝ) < 16)] using h
    have hbound : (16 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hlo]
    exact
      ⟨r, hr, (hrexp.trans hExp).trans hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hr hrd⟩
  · by_cases hmid : Real.log n ≤ 883 / 100
    · have hcert :=
        (Analysis.rationalLogIntervalCheck_sound
            (show Analysis.rationalLogIntervalCheck 19 5 32 (2944 / 1000) 3 = true from by
              decide +kernel)).1
      norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
      have hExp : Real.exp (Real.log n / 3) < 19 := by
        have h :=
          Real.exp_lt_exp.mpr
            (show Real.log n / 3 < Real.log (19 : ℝ) by linarith only [hmid, hcert])
        simpa only [Real.exp_log (by norm_num only : (0 : ℝ) < 19)] using h
      have hr19 : r < 19 := by exact_mod_cast (hrexp.trans_lt hExp)
      have hr17 : r ≤ 17 := by
        have hne : r ≠ 18 := by
          intro he
          subst r
          norm_num only [Nat.prime_def_lt] at hr
        omega
      have hbound : (17 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by
        nlinarith only [le_of_not_ge hsplit]
      exact
        ⟨r, hr, (Nat.cast_le.mpr hr17).trans hbound,
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hr hrd⟩
    · have hcert :=
        (Analysis.rationalLogIntervalCheck_sound
            (show Analysis.rationalLogIntervalCheck 23 5 32 (3134 / 1000) 4 = true from by
              decide +kernel)).1
      norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
      have hExp : Real.exp (Real.log n / 3) < 23 := by
        have h :=
          Real.exp_lt_exp.mpr
            (show Real.log n / 3 < Real.log (23 : ℝ) by linarith only [hhi, hcert])
        simpa only [Real.exp_log (by norm_num only : (0 : ℝ) < 23)] using h
      have hr23 : r < 23 := by exact_mod_cast (hrexp.trans_lt hExp)
      have hr19 : r ≤ 19 := by
        by_contra h
        have hnp : ∀ k ∈ Finset.Icc 20 22, ¬Nat.Prime k := by decide +kernel
        exact hnp r (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), by omega⟩) hr
      have hbound : (19 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by
        nlinarith only [le_of_not_ge hmid]
      exact
        ⟨r, hr, (Nat.cast_le.mpr hr19).trans hbound,
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hr hrd⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
