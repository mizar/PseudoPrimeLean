/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.PairedLocalSign
public import PseudoPrime.NumberTheory.PrimeFactorPairBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalSubgroupBounds

/-! # Uniform two-adic Korselt branch with at least four prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd n at least 10^141 with at least four distinct prime
factors has a failing prime base at most (283/1000)log(n)^2 when all factors
satisfy Korselt divisibility and have equal predecessor two-adic valuations.
Select a paired modulus no larger than sqrt(n), construct its proper sign
subgroup using the paired quadratic character, and reduce every strong pass.
No ambient index, local size, or supplied containment hypothesis is needed. -/
theorem exists_prime_witness_le_0283_of_four_primeFactors_uniform_twoAdic {n : ℕ} (hnOdd : Odd n)
    (hc : 4 ≤ n.primeFactors.card) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hv :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  obtain ⟨p, q, hp, hq, hpq, hpqn, hsize⟩ :=
    NumberTheory.exists_prime_pair_modulus_square_le (Nat.zero_lt_of_lt hn1) hc
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hpn : p ∣ n := (dvd_mul_right p q).trans hpqn
  have hqn : q ∣ n := (dvd_mul_left q p).trans hpqn
  have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn)
  have hqOdd := hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn)
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (hnOdd.ne_two_of_dvd_nat hpn).symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (hnOdd.ne_two_of_dvd_nat hqn).symm⟩
  let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
  obtain ⟨kp, hkp, hEp⟩ :=
    PrimeTest.canonical_sign_exponent_local_half hp.one_lt hpOdd hn1 hnOdd (hK p hp hpn)
  obtain ⟨kq, hkq, hEq⟩ :=
    PrimeTest.canonical_sign_exponent_local_half hq.one_lt hqOdd hn1 hnOdd (hK q hq hqn)
  rw [hv q p hq hp hqn hpn] at hEq
  have hproper :=
    PrimeTest.signSubgroup_pair_ne_top_of_local_half_odd hpOdd hqOdd hpq hkp hkq hEp hEq
  have hcontain :
    ∀ a : ℕ,
      PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
        ∃ v : (ZMod (p * q))ˣ,
          v ∈ PrimeTest.signSubgroup (p * q) E ∧ (v : ZMod (p * q)) = (a : ZMod (p * q)) := by
    intro a ha
    obtain ⟨u, hu, hua⟩ :=
      PrimeTest.strongMillerRabinPass_mem_signSubgroup hn1 hnOdd ha hp hpOdd hpn
    refine ⟨ZMod.unitsMap hpqn u, PrimeTest.signSubgroup_unitsMap_mem hpqn u hu, ?_⟩
    rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hpqn]
  have hsize' := hsize.trans (Nat.le_mul_of_pos_left n (by decide : 0 < 10 ^ 9))
  exact
    exists_prime_witness_le_0283_of_local_subgroup hnOdd
      (hp.two_le.trans (Nat.le_mul_of_pos_right p hq.pos)) hpqn (PrimeTest.signSubgroup (p * q) E)
      hproper hcontain hGRH hn hsize'

end PseudoPrime.PrimeTestBounds.MillerRabin
