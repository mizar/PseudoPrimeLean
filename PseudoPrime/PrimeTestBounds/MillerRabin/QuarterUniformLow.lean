/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltLogLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.LogScalePow22
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePairLocalData
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.NumberTheory.PrimeFactorPairClassification

/-! # Low-range uniform Korselt witnesses with coefficient one quarter -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd integer of logarithmic scale at least 8 with a prime divisor at most 13
has a rejecting prime below the one-quarter bound. The divisor itself is a witness. -/
theorem exists_prime_reject_quarter_divisor13 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ n) (hp13 : p ≤ 13) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb : (13 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp13).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd⟩

/-- An odd integer at least 410041 with a prime divisor at most 41 has a rejecting
prime below the one-quarter bound. A rational logarithm certificate supplies scale 12.9. -/
theorem exists_prime_reject_quarter_divisor41 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ n) (hp41 : p ≤ 41) (hlarge : 410041 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 410041 19 32 (129 / 10) 14 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 410041) (Nat.cast_le.mpr hlarge)
  have hL : (129 / 10 : ℝ) ≤ Real.log n := hcert.trans hlog
  have hb : (41 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp41).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd⟩

/-- A uniform Korselt triple with logarithm at most 15.2 has a rejecting prime
below the one-quarter bound. The finite classification reduces this to six inputs, each
handled by a certified small prime divisor. -/
theorem uniformKorselt_reject_quarter_low {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hU : Real.log n ≤ 76 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hL := uniformKorselt_log_ge_eight hu
  have hm := uniformKorselt_le_pow22_cases hu (le_pow22_of_log_le_152 hn hU)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h
  · subst n
    exact
      exists_prime_reject_quarter_divisor13 hn ho (by decide : Nat.Prime 7) (by decide : 7 ∣ 8911)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_quarter_divisor13 hn ho (by decide : Nat.Prime 13)
        (by decide : 13 ∣ 314821) (by decide) hL
  · subst n
    exact
      exists_prime_reject_quarter_divisor13 hn ho (by decide : Nat.Prime 13)
        (by decide : 13 ∣ 29341) (by decide) hL
  · subst n
    exact
      exists_prime_reject_quarter_divisor41 hn ho (by decide : Nat.Prime 19)
        (by decide : 19 ∣ 1024651) (by decide) (by decide)
  · subst n
    exact
      exists_prime_reject_quarter_divisor41 hn ho (by decide : Nat.Prime 41)
        (by decide : 41 ∣ 410041) (by decide) (by decide)
  · subst n
    have hcert :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1152271 20 32 (132 / 10) 15 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
    have hb : (43 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log (1152271 : ℕ)) ^ 2 := by nlinarith only [hcert]
    exact
      ⟨43, by decide, hb,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho (by decide) (by decide)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
