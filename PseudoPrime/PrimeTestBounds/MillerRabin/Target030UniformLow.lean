/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.LogScalePow22
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030EarlyBridge

/-! # Uniform Korselt triples on the low 0.30 range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input with logarithm at least 8 has a 0.30 rejecting prime when it
has a prime divisor at most 19. The divisor itself is the witness. -/
theorem exists_prime_reject_03_divisor19 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ n) (hp19 : p ≤ 19) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb : (19 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp19).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd⟩

/-- An odd input at least 410041 has a 0.30 rejecting prime when it has a
prime divisor at most 43. A rational logarithm certificate supplies scale 12. -/
theorem exists_prime_reject_03_divisor43 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ n) (hp43 : p ≤ 43) (hlarge : 410041 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 410041 19 32 12 14 = true from by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 410041) (Nat.cast_le.mpr hlarge)
  have hL : (12 : ℝ) ≤ Real.log n := hcert.trans hlog
  have hb : (43 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    ⟨p, hp, (Nat.cast_le.mpr hp43).trans hb,
      PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hd⟩

/-- A uniform Korselt triple at most `2^22` has a 0.30 rejecting prime from
logarithmic scale 8. Each of the six classified inputs has a sufficiently
small prime factor, whose primality and divisibility are checked exactly. -/
theorem uniformKorselt_reject_03_pow22 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hbound : n ≤ 2 ^ 22) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hm := uniformKorselt_le_pow22_cases hu hbound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h
  · subst n
    exact
      exists_prime_reject_03_divisor19 hn ho (by decide : Nat.Prime 7) (by decide : 7 ∣ 8911)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_03_divisor19 hn ho (by decide : Nat.Prime 13) (by decide : 13 ∣ 314821)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_03_divisor19 hn ho (by decide : Nat.Prime 13) (by decide : 13 ∣ 29341)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_03_divisor19 hn ho (by decide : Nat.Prime 19) (by decide : 19 ∣ 1024651)
        (by decide) hL
  · subst n
    exact
      exists_prime_reject_03_divisor43 hn ho (by decide : Nat.Prime 41) (by decide : 41 ∣ 410041)
        (by decide) (by decide)
  · subst n
    exact
      exists_prime_reject_03_divisor43 hn ho (by decide : Nat.Prime 43) (by decide : 43 ∣ 1152271)
        (by decide) (by decide)

/-- Under GRH, every odd uniform Korselt triple with logarithm in `[8, 39.4]`
has a 0.30 rejecting prime. The finite classification covers the range through
15 and the eight certified local corrections cover the remainder. -/
theorem uniformKorselt_reject_03_low {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 197 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h15 : Real.log n ≤ 15
  · exact uniformKorselt_reject_03_pow22 hn ho hu (le_pow22_of_log_le_15 hn h15) hL
  · exact exists_prime_reject_03_uniform_low hn ho hu hGRH hL hU (Or.inr (le_of_not_ge h15))

end PseudoPrime.PrimeTestBounds.MillerRabin
