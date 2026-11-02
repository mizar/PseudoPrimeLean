/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHigh
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsFactorBounds
public import PseudoPrime.NumberTheory.PrimeFactorPairClassification

/-! # High-range four-ninths witnesses for all odd composites -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite `n > 1` with `log n ≥ 1024` has a prime
MR rejecting base at most `(4 / 9) * log n ^ 2`. If the number of prime factors
with multiplicity is at least three, use the total-factor bound. Otherwise it
is exactly two, and the ordered prime-factor pair is either a square or a
product of distinct primes, both covered by the high-range construction. -/
theorem exists_prime_witness_high_four_ninths {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (1024 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hk : 3 ≤ ArithmeticFunction.cardFactors n
  · exact exists_prime_witness_four_ninths_of_factors hn ho hc hGRH hk
  · have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
    have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
      hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
    have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
      Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
    have hkeq : ArithmeticFunction.cardFactors n = 2 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hk)) hk2
    obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
      NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hkeq
    have hpdiv : p ∣ n := by
      rw [hprod]; exact dvd_mul_right p q
    have hqdiv : q ∣ n := by
      rw [hprod]; exact dvd_mul_left q p
    have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpdiv
    have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqdiv
    rcases hpq.eq_or_lt with heq | hlt
    · have hsquare : n = p ^ 2 := by rw [hprod, ← heq, pow_two]
      exact exists_prime_witness_high_square hn ho hp hp2 hsquare hGRH.riemann hL
    · exact exists_prime_high_distinct_factors hn ho hp hq hlt hq2 hprod hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
