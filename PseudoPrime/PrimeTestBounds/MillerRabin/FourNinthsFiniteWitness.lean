/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCover
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsLowSquareCover
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsLowSemiprimeCover
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighWitness

/-! # Four-ninths witnesses above the finite entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with `log n ≥ 8.3` has an MR rejecting
prime within the four-ninths bound. Classify the prime factors and combine
the low, analytic-cell, and uniform high-range witness constructions. -/
theorem exists_prime_witness_four_ninths_log_ge {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (83 / 10 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hhigh : (1024 : ℝ) ≤ Real.log n
  · exact exists_prime_witness_high_four_ninths hn ho hc hGRH hhigh
  have hmid : Real.log n ≤ 1024 := (lt_of_not_ge hhigh).le
  by_cases hk : 3 ≤ ArithmeticFunction.cardFactors n
  · exact exists_prime_witness_four_ninths_of_factors hn ho hc hGRH hk
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
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
    by_cases hlow : Real.log n ≤ 56
    · exact exists_prime_witness_low_square hn ho hp hp2 hsquare hL hlow
    · exact
        exists_prime_witness_analytic_square hn ho hp hp2 hsquare hGRH.riemann
          (lt_of_not_ge hlow).le hmid
  · by_cases hsmall : Real.log q ≤ (2 / 3 : ℝ) * Real.log n
    · exact semiprime_small_factor_log hn ho hp hq hlt hprod hGRH hsmall
    · have hlarge := lt_of_not_ge hsmall
      by_cases hlow : Real.log n ≤ 50
      · exact exists_prime_witness_low_semiprime hn ho hp hq hq2 hprod hL hlow hlarge
      · exact
          exists_prime_witness_analytic_semiprime hn ho hp hq hq2 hprod hGRH.riemann
            (lt_of_not_ge hlow).le hmid hlarge

end PseudoPrime.PrimeTestBounds.MillerRabin
