/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEnvelopeLower

/-! # Local envelope witness for a two-prime divisor -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd input with a divisor `p*q` formed from two primes has a rejecting
prime within the common local envelope at any scale at least `log (p*q)`. Factor three
is a direct witness; otherwise the repeated, Korselt and two-adic cases provide a proper
local subgroup whose passing residues yield a witness through the common envelope. -/
theorem exists_prime_reject_pair_local {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpqdiv : p * q ∣ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {S : ℝ}
    (hS : Real.log ((p * q : ℕ) : ℝ) ≤ S) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ localFullEnvelope S ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_mul_right p q).trans hpqdiv
  have hqn : q ∣ n := (dvd_mul_left q p).trans hpqdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hqn
  have hpOdd := hp.odd_of_ne_two hp2
  have hqOdd := hq.odd_of_ne_two hq2
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le hp2.symm)
  have hq3 : 3 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_ne hq.two_le hq2.symm)
  have hpair9 : 9 ≤ p * q := (by norm_num only : 9 = 3 * 3) ▸ Nat.mul_le_mul hp3 hq3
  have hlog9 : Real.log 9 ≤ Real.log ((p * q : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hpair9)
  have hsmall := three_le_local_full (hlog9.trans hS)
  by_cases hpIs3 : p = 3
  · subst p
    exact
      ⟨3, Nat.prime_three, hsmall,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hpn⟩
  by_cases hqIs3 : q = 3
  · subst q
    exact
      ⟨3, Nat.prime_three, hsmall,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hqn⟩
  have hp5 := hp.five_le_of_ne_two_of_ne_three hp2 hpIs3
  have hq5 := hq.five_le_of_ne_two_of_ne_three hq2 hqIs3
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le hp2.symm⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le hq2.symm⟩
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have transfer (s : ℕ) [NeZero s] (hs : 5 ≤ s) (hsn : s ∣ n) (hsp : s ≤ p * q)
    (H : Subgroup (ZMod s)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod s)ˣ, u ∈ H ∧ (u : ZMod s) = (a : ZMod s)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ localFullEnvelope S ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
    have hlog : Real.log s ≤ S :=
      (Real.log_le_log (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num only : 0 < 5) hs))
            (Nat.cast_le.mpr hsp)).trans
        hS
    exact exists_prime_reject_local_full hn ho hs hsn H hH hpass hGRH hlog
  by_cases heq : p = q
  · subst q
    have hdiv : p ^ 2 ∣ n := by simpa only [pow_two] using hpqdiv
    have hi := PrimeTest.prime_le_local_square_powerKernel_index hn hp hp2 hdiv
    have hproper : (powMonoidHom (n - 1) : (ZMod (p * p))ˣ →* (ZMod (p * p))ˣ).ker ≠ ⊤ := by
      intro ht
      rw [pow_two, ht, Subgroup.index_top] at hi
      exact (not_le_of_gt hp.one_lt) hi
    exact
      transfer (p * p) (le_trans (by decide : 5 ≤ 9) hpair9) hpqdiv (le_refl _) _ hproper
        (fun a ha ↦ PrimeTest.strongMR_local_divisorKernel hn ho hpqdiv ha)
  by_cases hpK : p - 1 ∣ n - 1
  · by_cases hqK : q - 1 ∣ n - 1
    · rcases lt_trichotomy (padicValNat 2 (p - 1)) (padicValNat 2 (q - 1)) with hv | hv | hv
      · exact
          transfer q hq5 hqn (Nat.le_mul_of_pos_left q hp.pos) _
            (PrimeTest.local_half_powerKernel_ne_top hqOdd)
            (fun a ha ↦
              PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn ho hqOdd hpOdd hqn hpn hv
                ha)
      · let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
        obtain ⟨kp, hkp, hEp⟩ :=
          PrimeTest.canonical_sign_exponent_local_half hp.one_lt hpOdd hn ho hpK
        obtain ⟨kq, hkq, hEq⟩ :=
          PrimeTest.canonical_sign_exponent_local_half hq.one_lt hqOdd hn ho hqK
        rw [← hv] at hEq
        have hproper :=
          PrimeTest.signSubgroup_pair_ne_top_of_local_half_odd hpOdd hqOdd heq hkp hkq hEp hEq
        apply
          transfer (p * q) (le_trans (by decide : 5 ≤ 9) hpair9) hpqdiv (le_refl _)
            (PrimeTest.signSubgroup (p * q) E) hproper
        intro a ha
        obtain ⟨u, hu, hua⟩ :=
          PrimeTest.strongMillerRabinPass_mem_signSubgroup hn ho ha hp hpOdd hpn
        refine ⟨ZMod.unitsMap hpqdiv u, PrimeTest.signSubgroup_unitsMap_mem hpqdiv u hu, ?_⟩
        rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hpqdiv]
      · exact
          transfer p hp5 hpn (Nat.le_mul_of_pos_right p hq.pos) _
            (PrimeTest.local_half_powerKernel_ne_top hpOdd)
            (fun a ha ↦
              PrimeTest.strongPass_mem_local_half_kernel_of_twoAdic_lt hn ho hpOdd hqOdd hpn hqn hv
                ha)
    · exact
        transfer q hq5 hqn (Nat.le_mul_of_pos_left q hp.pos) _
          (NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hqK)
          (fun a ha ↦ PrimeTest.strongMR_local_primeKernel hn ho hqn ha)
  · exact
      transfer p hp5 hpn (Nat.le_mul_of_pos_right p hq.pos) _
        (NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hpK)
        (fun a ha ↦ PrimeTest.strongMR_local_primeKernel hn ho hpn ha)

end PseudoPrime.PrimeTestBounds.MillerRabin
