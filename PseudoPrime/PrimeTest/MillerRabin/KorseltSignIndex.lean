/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.KorseltHalfExponent
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupCardinality

/-! # Exact index four for three local half-exponent sign factors

Each local power image has cardinality two. CRT and the common-sign fiber
formula give index four for three pairwise coprime odd prime factors.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- An odd multiple of a local half exponent has totient-to-gcd ratio two.
Factor the gcd by p/2 and use coprimality of the odd quotient with two.
This is the local image-size certificate used by the exact index formula. -/
theorem totient_div_gcd_eq_two_of_local_half_odd {p E k : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (hpOdd : Odd p) (hk : Odd k) (hE : E = (p / 2) * k) : p.totient / p.totient.gcd E = 2 := by
  have hp : p.Prime := Fact.out
  have hp2 : p / 2 * 2 = p - 1 := by
    obtain ⟨m, hm⟩ := hpOdd
    rw [hm, Nat.mul_add_div (by decide : 0 < 2)]
    simp only [Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero]
    rw [Nat.add_sub_cancel_right]
    exact Nat.mul_comm m 2
  have hhalf : 0 < p / 2 := Nat.div_pos (Nat.le_of_lt (Fact.out : 2 < p)) (by decide)
  rw [Nat.totient_prime hp, hE, ← hp2, Nat.gcd_mul_left, hk.coprime_two_left.gcd_eq_one,
    Nat.mul_one, Nat.mul_div_cancel_left _ hhalf]

/-- The local half-exponent odd-multiple power map has a two-element image.
Apply the cyclic prime-unit-group cardinality formula and the exact gcd ratio.
This counts the local factors in the CRT power image. -/
theorem card_unitPowerImage_eq_two_of_local_half_odd {p E k : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (hpOdd : Odd p) (hk : Odd k) (hE : E = (p / 2) * k) :
    Nat.card (powMonoidHom E : (ZMod p)ˣ →* (ZMod p)ˣ).range = 2 := by
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    totient_div_gcd_eq_two_of_local_half_odd hpOdd hk hE]

/-- At an odd prime, a local half-exponent odd multiple has a negative-one preimage.
The signs are distinct and the cyclic image has even cardinality two.
This supplies the common negative fiber in the global index calculation. -/
theorem exists_neg_one_root_of_local_half_odd {p E k : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (hpOdd : Odd p) (hk : Odd k) (hE : E = (p / 2) * k) : ∃ u : (ZMod p)ˣ, u ^ E = -1 := by
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := fun h ↦ ZMod.neg_one_ne_one (congrArg Units.val h)
  apply NumberTheory.exists_unit_pow_eq_neg_one_of_even_image hne
  rw [totient_div_gcd_eq_two_of_local_half_odd hpOdd hk hE]

/-- For three pairwise coprime odd primes, an exponent that is an odd multiple
of every local half exponent has sign-subgroup index exactly four. Combine
local negative roots by CRT and multiply the three two-element power images;
the global sign fiber contributes one factor of two. This is the exact
arithmetic index needed by the Gaussian three-prime witness branch. -/
theorem index_signSubgroup_three_primes_eq_four_of_local_half_odd {p q r E kp kq kr : ℕ}
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hkp : Odd kp) (hkq : Odd kq) (hkr : Odd kr)
    (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) (hEr : E = (r / 2) * kr) (hpq : p.Coprime q)
    (hpr : p.Coprime r) (hqr : q.Coprime r) : (signSubgroup (p * q * r) E).index = 4 := by
  let : NeZero (p * q) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  let : NeZero (p * q * r) := ⟨mul_ne_zero (NeZero.ne (p * q)) (NeZero.ne r)⟩
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hr : r.Prime := Fact.out
  have hprod : 2 < p * q * r :=
    (Fact.out : 2 < p).trans_le
      ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : Fact (2 < p * q * r) := ⟨hprod⟩
  have hne : (-1 : (ZMod (p * q * r))ˣ) ≠ 1 := fun h ↦ ZMod.neg_one_ne_one (congrArg Units.val h)
  have hrootpq :=
    NumberTheory.exists_unit_pow_eq_neg_one_coprime_mul hpq
      (exists_neg_one_root_of_local_half_odd hpOdd hkp hEp)
      (exists_neg_one_root_of_local_half_odd hqOdd hkq hEq)
  have hi :=
    two_mul_index_signSubgroup_coprime_mul (hpr.mul_left hqr) hne hrootpq
      (exists_neg_one_root_of_local_half_odd hrOdd hkr hEr)
  rw [NumberTheory.card_unitPowerImage_coprime_mul hpq,
    card_unitPowerImage_eq_two_of_local_half_odd hpOdd hkp hEp,
    card_unitPowerImage_eq_two_of_local_half_odd hqOdd hkq hEq,
    card_unitPowerImage_eq_two_of_local_half_odd hrOdd hkr hEr] at hi
  linarith only [hi]

end PseudoPrime.PrimeTest
