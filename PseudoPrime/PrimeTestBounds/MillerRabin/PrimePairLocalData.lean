/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeFactorLocalEnvelope

/-! # Proper local subgroups from two prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A two-prime divisor of an odd input either contains the prime three or
provides a proper local subgroup at a divisor no larger than the product.
Repeated, non-Korselt, and equal or unequal two-adic cases supply the subgroup. -/
theorem prime_pair_local_data {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hd : p * q ∣ n) :
    3 ∣ n ∨
      ∃ s : ℕ,
        0 < s ∧
          s ∣ n ∧
          s ≤ p * q ∧
          ∃ H : Subgroup (ZMod s)ˣ,
            H ≠ ⊤ ∧
              ∀ a : ℕ,
                PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
                  ∃ u : (ZMod s)ˣ, u ∈ H ∧ (u : ZMod s) = (a : ZMod s) := by
  have hpn : p ∣ n := (dvd_mul_right p q).trans hd
  have hqn : q ∣ n := (dvd_mul_left q p).trans hd
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqn
  have hpOdd := hp.odd_of_ne_two hp2
  have hqOdd := hq.odd_of_ne_two hq2
  by_cases hp3 : p = 3
  · exact Or.inl (hp3 ▸ hpn)
  by_cases hq3 : q = 3
  · exact Or.inl (hq3 ▸ hqn)
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le hp2.symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le hq2.symm⟩
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  by_cases heq : p = q
  · subst q
    have hdiv : p ^ 2 ∣ n := by simpa only [pow_two] using hd
    have hi := PrimeTest.prime_le_local_square_powerKernel_index hn hp hp2 hdiv
    have hproper : (powMonoidHom (n - 1) : (ZMod (p * p))ˣ →* (ZMod (p * p))ˣ).ker ≠ ⊤ := by
      intro ht
      rw [pow_two, ht, Subgroup.index_top] at hi
      exact (not_le_of_gt hp.one_lt) hi
    exact
      Or.inr
        ⟨p * p, mul_pos hp.pos hp.pos, hd, le_rfl, _, hproper, fun a ha ↦
          PrimeTest.strongMR_local_divisorKernel hn ho hd ha⟩
  by_cases hpK : p - 1 ∣ n - 1
  · by_cases hqK : q - 1 ∣ n - 1
    · rcases lt_trichotomy (padicValNat 2 (p - 1)) (padicValNat 2 (q - 1)) with hv | hv | hv
      · exact
          Or.inr
            ⟨q, hq.pos, hqn, Nat.le_mul_of_pos_left q hp.pos, _,
              PrimeTest.local_half_powerKernel_ne_top hqOdd, fun a ha ↦
              PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn ho hqOdd hpOdd hqn hpn hv
                ha⟩
      · let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
        obtain ⟨kp, hkp, hEp⟩ :=
          PrimeTest.canonical_sign_exponent_local_half hp.one_lt hpOdd hn ho hpK
        obtain ⟨kq, hkq, hEq⟩ :=
          PrimeTest.canonical_sign_exponent_local_half hq.one_lt hqOdd hn ho hqK
        rw [← hv] at hEq
        have hproper :=
          PrimeTest.signSubgroup_pair_ne_top_of_local_half_odd hpOdd hqOdd heq hkp hkq hEp hEq
        refine Or.inr ⟨p * q, mul_pos hp.pos hq.pos, hd, le_rfl, _, hproper, ?_⟩
        intro a ha
        obtain ⟨u, hu, hua⟩ :=
          PrimeTest.strongMillerRabinPass_mem_signSubgroup hn ho ha hp hpOdd hpn
        refine ⟨ZMod.unitsMap hd u, PrimeTest.signSubgroup_unitsMap_mem hd u hu, ?_⟩
        rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hd]
      · exact
          Or.inr
            ⟨p, hp.pos, hpn, Nat.le_mul_of_pos_right p hq.pos, _,
              PrimeTest.local_half_powerKernel_ne_top hpOdd, fun a ha ↦
              PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn ho hpOdd hqOdd hpn hqn hv
                ha⟩
    · exact
        Or.inr
          ⟨q, hq.pos, hqn, Nat.le_mul_of_pos_left q hp.pos, _,
            NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hqK, fun a ha ↦
            PrimeTest.strongMR_local_primeKernel hn ho hqn ha⟩
  · exact
      Or.inr
        ⟨p, hp.pos, hpn, Nat.le_mul_of_pos_right p hq.pos, _,
          NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hpK, fun a ha ↦
          PrimeTest.strongMR_local_primeKernel hn ho hpn ha⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
