/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.KorseltSignIndex

/-! # Passing residues at prime factors with unequal two-adic valuations

A smaller predecessor valuation bounds the two-adic part of passing orders.
At a larger-valuation prime factor, every strong pass lies in the local
half-exponent kernel, which is the proper quadratic-residue subgroup.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- If a nonzero exponent has smaller two-adic valuation than N, gcd(N,E)
divides N/2. The quotient N/gcd(N,E) is even; factor out two before dividing.
This gives the local half-exponent divisibility needed for a quadratic-residue test. -/
theorem gcd_dvd_half_of_twoAdic_lt {N E : ℕ} (hE : E ≠ 0) (hv : padicValNat 2 E < padicValNat 2 N) :
    N.gcd E ∣ N / 2 := by
  obtain ⟨k, hk⟩ := NumberTheory.two_dvd_div_gcd_of_twoAdic_lt hE hv
  have hprod := Nat.div_mul_cancel (Nat.gcd_dvd_left N E)
  have hN : N = (N.gcd E * k) * 2 := by
    rw [hk] at hprod
    nlinarith only [hprod]
  have hhalf : N / 2 = N.gcd E * k := by
    calc
      N / 2 = ((N.gcd E * k) * 2) / 2 := congrArg (fun x : ℕ ↦ x / 2) hN
      _ = _ := Nat.mul_div_cancel _ (by decide : 0 < 2)
  rw [hhalf]
  exact dvd_mul_right _ _

/-- At an odd prime, a unit killed by a nonzero exponent of smaller two-adic
valuation than p-1 has half-exponent power one. Its order divides both p-1 and E,
hence their gcd and the local half exponent. This identifies local square residues. -/
theorem unit_half_pow_eq_one_of_twoAdic_lt {p E : ℕ} [Fact p.Prime] (hpOdd : Odd p) (hE : E ≠ 0)
    (hv : padicValNat 2 E < padicValNat 2 (p - 1)) (u : (ZMod p)ˣ) (hpow : u ^ E = 1) :
    u ^ (p / 2) = 1 := by
  have hdE := orderOf_dvd_of_pow_eq_one hpow
  have hdP := orderOf_dvd_of_pow_eq_one (ZMod.units_pow_card_sub_one_eq_one p u)
  have hdG := Nat.dvd_gcd hdP hdE
  have hdH := hdG.trans (gcd_dvd_half_of_twoAdic_lt hE hv)
  have hp2 : (p - 1) / 2 = p / 2 := by
    obtain ⟨k, hk⟩ := hpOdd
    rw [hk, Nat.add_sub_cancel_right, Nat.mul_add_div (by decide : 0 < 2)]
    simp only [Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [hp2] at hdH
  exact orderOf_dvd_iff_pow_eq_one.mp hdH

/-- A common-sign subgroup reduces into the local half-exponent kernel if
the two-adic valuation of twice its exponent is smaller than that of p-1.
Square the common sign, reduce the resulting power identity and use order
divisibility. This is the local containment for the unequal-valuation branch. -/
theorem signSubgroup_unit_local_half_pow_eq_one_of_twoAdic_lt {n p E : ℕ} [Fact p.Prime]
    (hpOdd : Odd p) (hpn : p ∣ n) (hE : E ≠ 0) (hv : padicValNat 2 (2 * E) < padicValNat 2 (p - 1))
    (u : (ZMod n)ˣ) (hu : u ∈ signSubgroup n E) : (ZMod.unitsMap hpn u) ^ (p / 2) = 1 := by
  have hpow : u ^ (2 * E) = 1 := by
    change u ^ E = 1 ∨ u ^ E = -1 at hu
    rw [Nat.mul_comm 2 E, pow_mul]
    rcases hu with h | h
    · rw [h, one_pow]
    · rw [h, neg_one_sq]
  have hm := congrArg (ZMod.unitsMap hpn) hpow
  rw [map_pow, map_one] at hm
  exact unit_half_pow_eq_one_of_twoAdic_lt hpOdd (mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hE) hv _ hm

/-- If two odd prime factors q,p have strictly increasing predecessor
two-adic valuations, every ambient strong MR pass reduces into the p/2-power
kernel modulo p. The smaller factor supplies the canonical common-sign subgroup;
its doubled exponent retains that smaller valuation. This removes a supplied
local square-residue premise from the unequal-valuation witness branch. -/
theorem strongMillerRabinPass_mem_local_half_kernel_of_twoAdic_lt {n p q a : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hn : 1 < n) (hnOdd : Odd n) (hpOdd : Odd p) (hqOdd : Odd q) (hpn : p ∣ n)
    (hqn : q ∣ n) (hv : padicValNat 2 (q - 1) < padicValNat 2 (p - 1))
    (hpass : StrongMillerRabinPass n (a : ZMod n)) :
    ∃ v : (ZMod p)ˣ,
      v ∈ (powMonoidHom (p / 2) : (ZMod p)ˣ →* (ZMod p)ˣ).ker ∧ (v : ZMod p) = (a : ZMod p) := by
  let t := padicValNat 2 (q - 1)
  let d := Nat.divMaxPow (n - 1) 2
  let E := 2 ^ (t - 1) * d
  have ht : 0 < t := (odd_sub_canonical_decomp (Fact.out : q.Prime).one_lt hqOdd).1
  have hd : Odd d := (odd_sub_canonical_decomp hn hnOdd).2.1
  have hE : E ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hd.pos.ne'
  have he : 2 * E = 2 ^ t * d := by
    dsimp only [E]
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel ht]
  have hval : padicValNat 2 (2 * E) = t := by
    rw [he, padicValNat.mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hd.pos.ne',
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hd.not_two_dvd_nat, Nat.add_zero]
  obtain ⟨u, hu, hua⟩ :=
    strongMillerRabinPass_mem_signSubgroup hn hnOdd hpass (Fact.out : q.Prime) hqOdd hqn
  refine ⟨ZMod.unitsMap hpn u, ?_, ?_⟩
  · exact signSubgroup_unit_local_half_pow_eq_one_of_twoAdic_lt hpOdd hpn hE (hval.trans_lt hv) u hu
  · rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hpn]

/-- At an odd prime, the half-exponent power kernel is a proper subgroup.
Its cyclic power image has exactly two elements, so its kernel index is two.
This supplies properness for the local quadratic-residue LLS comparison. -/
theorem local_half_powerKernel_ne_top {p : ℕ} [Fact p.Prime] (hpOdd : Odd p) :
    (powMonoidHom (p / 2) : (ZMod p)ˣ →* (ZMod p)ˣ).ker ≠ ⊤ := by
  have hp : p.Prime := Fact.out
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm (hpOdd.ne_two_of_dvd_nat (dvd_refl p)))⟩
  have hi : (powMonoidHom (p / 2) : (ZMod p)ˣ →* (ZMod p)ˣ).ker.index = 2 := by
    rw [Subgroup.index_ker]
    exact
      card_unitPowerImage_eq_two_of_local_half_odd (k := 1) hpOdd (by decide : Odd 1)
        (by rw [Nat.mul_one])
  intro ht
  rw [ht, Subgroup.index_top] at hi
  norm_num only at hi

end PseudoPrime.PrimeTest
