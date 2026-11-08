/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformLow

/-! # Low-range uniform Korselt witnesses with coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd integer of logarithmic scale at least 8 with a prime divisor at most 13
has a rejecting prime below the 0.28 bound. The divisor itself is a witness. -/
theorem exists_prime_reject_028_divisor13 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ n) (hp13 : p ≤ 13) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb : (13 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp13).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd⟩

/-- An odd integer at least 410041 with a prime divisor at most 46 has a rejecting
prime below the 0.28 bound. A rational logarithm certificate supplies scale 12.9. -/
theorem exists_prime_reject_028_divisor46 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ n) (hp46 : p ≤ 46) (hlarge : 410041 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 410041 19 32 (129 / 10) 14 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 410041) (Nat.cast_le.mpr hlarge)
  have hL : (129 / 10 : ℝ) ≤ Real.log n := hcert.trans hlog
  have hb : (46 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp46).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd⟩

/-- A uniform Korselt triple with logarithm between 8 and 15 has a rejecting prime
below the 0.28 bound. The finite classification reduces this to six inputs, each
handled by a certified small prime divisor. -/
theorem uniformKorselt_reject_028_low {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hm := uniformKorselt_le_pow22_cases hu (le_pow22_of_log_le_15 hn hU)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h
  · subst n
    exact
      exists_prime_reject_028_divisor13 hn ho (by decide : Nat.Prime 7) (by decide : 7 ∣ 8911)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_028_divisor13 hn ho (by decide : Nat.Prime 13) (by decide : 13 ∣ 314821)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_028_divisor13 hn ho (by decide : Nat.Prime 13) (by decide : 13 ∣ 29341)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_028_divisor46 hn ho (by decide : Nat.Prime 19) (by decide : 19 ∣ 1024651)
        (by decide) (by decide)
  · subst n
    exact
      exists_prime_reject_028_divisor46 hn ho (by decide : Nat.Prime 41) (by decide : 41 ∣ 410041)
        (by decide) (by decide)
  · subst n
    exact
      exists_prime_reject_028_divisor46 hn ho (by decide : Nat.Prime 43) (by decide : 43 ∣ 1152271)
        (by decide) (by decide)

/-- A proper local subgroup at a divisor of logarithmic size at most two thirds
of the input gives a 0.28 witness on scales 15 through 16. The radius-8 anchor
gives a prime at most 64, and primality improves this to 61. -/
theorem exists_prime_reject_028_local_15_16 {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (15 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 16) (hq : Real.log q ≤ (2 / 3 : ℝ) * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hpbound, hfail⟩ :=
    exists_prime_reject_target030_anchor hn ho hqn H hH hpass hGRH (b := 8) (d := 324969 / 100000)
      (j := 3) (by decide +kernel) hq
  have hmax : max (8 : ℝ) ((2 / 3 : ℝ) * Real.log n - 324969 / 100000) ≤ 8 := by
    apply max_le le_rfl
    linarith only [hU]
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hpbound
  have hp64 : (p : ℝ) ≤ 64 := by
    nlinarith only [hpbound, hmax, le_max_left (8 : ℝ) ((2 / 3 : ℝ) * Real.log n - 324969 / 100000)]
  have hp64n : p ≤ 64 := by exact_mod_cast hp64
  have hp61 : p ≤ 61 := by
    by_contra h
    have hnp : ∀ k ∈ Finset.Icc 62 64, ¬Nat.Prime k := by decide +kernel
    exact hnp p (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), hp64n⟩) hp
  have hb : (61 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact ⟨p, hp, (Nat.cast_le.mpr hp61).trans hb, hfail⟩

/-- Under GRH, an odd integer with at least three prime factors counted with
multiplicity has a 0.28 witness on logarithmic scales 15 through 16. The two
smallest factors provide a divisor to which the local subgroup bound applies. -/
theorem exists_prime_reject_028_three_15_16 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hL : (15 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 16) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
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
  have hratio : 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) ≤ 2 * Real.log n / 3 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg n))
      (by norm_num only) hkR
  rcases prime_pair_local_data hn ho hp hq hd with hthree | ⟨s, hs, hsn, hsp, H, hproper, hpass⟩
  · have hbound : (3 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero s := ⟨Nat.ne_zero_of_lt hs⟩
    have hslog : Real.log s ≤ (2 / 3 : ℝ) * Real.log n := by
      have h :=
        (Real.log_le_log (Nat.cast_pos.mpr hs) (Nat.cast_le.mpr hsp)).trans (hlog.trans hratio)
      linarith only [h]
    exact exists_prime_reject_028_local_15_16 hn ho hsn H hproper hpass hGRH hL hU hslog

end PseudoPrime.PrimeTestBounds.MillerRabin
