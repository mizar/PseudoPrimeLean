/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel

/-! # Local Fermat index controls prime-factor size

For a composite cofactor m>1, the local (p*m-1)-power kernel modulo p
has index k with p²≤k*p*m. The predecessor gcd reduces to that of m-1.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- For p,m>1, the predecessor gcd of p*m and p equals that of m and p.
Expand p*m-1 as (m-1)+(p-1)*m and apply the Euclidean gcd identity.
This identifies the local kernel quotient with the cofactor quotient. -/
theorem gcd_predecessor_mul_eq_cofactor {p m : ℕ} (hp : 1 < p) (hm : 1 < m) :
    (p - 1).gcd (p * m - 1) = (p - 1).gcd (m - 1) := by
  have hpred : p * m - 1 = (m - 1) + (p - 1) * m := by
    nlinarith only [Nat.sub_add_cancel hp.le, Nat.sub_add_cancel hm.le,
      Nat.sub_add_cancel (hp.le.trans (Nat.le_mul_of_pos_right p (Nat.zero_lt_of_lt hm)))]
  rw [hpred, Nat.gcd_add_mul_left_right]

/-- For p,m>1, p² is bounded by p*m times the local predecessor gcd quotient.
The gcd divides m-1, so p-1 divides k*(m-1); positivity gives p≤k*m.
Multiply by p. This is the arithmetic size bound for the non-Korselt local branch. -/
theorem prime_factor_square_le_local_gcd_quotient_mul {p m : ℕ} (hp : 1 < p) (hm : 1 < m) :
    p ^ 2 ≤ ((p - 1) / (p - 1).gcd (p * m - 1)) * (p * m) := by
  rw [gcd_predecessor_mul_eq_cofactor hp hm]
  let k := (p - 1) / (p - 1).gcd (m - 1)
  have hkg : k * (p - 1).gcd (m - 1) = p - 1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, zero_mul] at hkg
    exact Nat.sub_ne_zero_of_lt hp hkg.symm
  have hd := Nat.mul_dvd_mul_left k (Nat.gcd_dvd_right (p - 1) (m - 1))
  rw [hkg] at hd
  have hsmall := Nat.le_of_dvd (Nat.mul_pos hk (Nat.sub_pos_of_lt hm)) hd
  have hupper : p ≤ k * m := by
    nlinarith only [hsmall, hk, Nat.sub_add_cancel hp.le, Nat.sub_add_cancel hm.le]
  calc
    p ^ 2 = p * p := pow_two p
    _ ≤ p * (k * m) := Nat.mul_le_mul_left p hupper
    _ = k * (p * m) := by ring

/-- At a prime p and cofactor m>1, p² is at most p*m times the index
of the ambient-predecessor power kernel modulo p. Apply the cyclic prime
unit-group index formula and the cofactor gcd inequality.
This replaces the local modulus size premise by a local subgroup index bound. -/
theorem prime_factor_square_le_local_powerKernel_index_mul {p m : ℕ} [Fact p.Prime] (hm : 1 < m) :
    p ^ 2 ≤ (powMonoidHom (p * m - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker.index * (p * m) := by
  rw [Subgroup.index_ker, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
  exact prime_factor_square_le_local_gcd_quotient_mul (Fact.out : p.Prime).one_lt hm

/-- A prime-factor ambient-power kernel has index at most that of any
ambient subgroup contained in the Fermat subgroup. Pull the local kernel back
along the surjective unit reduction, use containment, and compare finite indices.
This transfers the finite global index bound into a local modulus size bound. -/
theorem local_powerKernel_index_le_of_le_fermat {n p : ℕ} [NeZero n] [Fact p.Prime] (hpn : p ∣ n)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ fermatSubgroup n) :
    (powMonoidHom (n - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker.index ≤ H.index := by
  let K := (powMonoidHom (n - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
  have hsub : H ≤ K.comap (ZMod.unitsMap hpn) := by
    intro u hu
    have hv := hH hu
    change u ^ (n - 1) = 1 at hv
    change (ZMod.unitsMap hpn u) ^ (n - 1) = 1
    rw [← map_pow, hv, map_one]
  have hd := Subgroup.index_dvd_of_le hsub
  rw [K.index_comap_of_surjective (ZMod.unitsMap_surjective hpn)] at hd
  have hi : 0 < H.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  exact Nat.le_of_dvd hi hd

/-- A sign subgroup lies in the ambient Fermat subgroup when twice its
exponent divides n-1. A common sign raised to an even multiple is one.
This supplies the containment needed by the local index transfer. -/
theorem signSubgroup_le_fermatSubgroup_of_two_mul_dvd {n E : ℕ} (hdiv : 2 * E ∣ n - 1) :
    signSubgroup n E ≤ fermatSubgroup n := by
  intro u hu
  change u ^ E = 1 ∨ u ^ E = -1 at hu
  obtain ⟨k, hk⟩ := hdiv
  change u ^ (n - 1) = 1
  rw [hk, Nat.mul_comm 2 E, Nat.mul_assoc, pow_mul]
  rcases hu with h | h
  · rw [h, one_pow]
  · rw [h]
    exact Even.neg_one_pow ⟨k, two_mul k⟩

/-- At any nonzero divisor modulus, the ambient-predecessor power-kernel
index is at most the index of an ambient subgroup lying in the Fermat subgroup.
Use the surjective unit reduction and the finite index divisibility formula.
This generalizes the local index transfer to prime-square moduli. -/
theorem local_divisor_powerKernel_index_le_of_le_fermat {n q : ℕ} [NeZero n] [NeZero q]
    (hqn : q ∣ n) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ fermatSubgroup n) :
    (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker.index ≤ H.index := by
  let K := (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker
  have hsub : H ≤ K.comap (ZMod.unitsMap hqn) := by
    intro u hu
    have hv := hH hu
    change u ^ (n - 1) = 1 at hv
    change (ZMod.unitsMap hqn u) ^ (n - 1) = 1
    rw [← map_pow, hv, map_one]
  have hd := Subgroup.index_dvd_of_le hsub
  rw [K.index_comap_of_surjective (ZMod.unitsMap_surjective hqn)] at hd
  have hi : 0 < H.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  exact Nat.le_of_dvd hi hd

/-- A Korselt prime divisor of a composite modulus is at most its square root.
The cofactor exceeds one, and Korselt divisibility makes the predecessor gcd
quotient one in the proved prime-factor size inequality.
This supplies a local modulus bound independent of the finite-index cutoff. -/
theorem prime_factor_square_le_of_korselt {n p : ℕ} [Fact p.Prime] (hn : 1 < n) (hcomp : ¬n.Prime)
    (hpn : p ∣ n) (hdiv : p - 1 ∣ n - 1) : p ^ 2 ≤ n := by
  obtain ⟨m, rfl⟩ := hpn
  have hp : p.Prime := Fact.out
  have hnpos : 0 < p * m := Nat.zero_lt_of_lt hn
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun hm ↦ Nat.ne_zero_of_lt hnpos (by rw [hm, mul_zero]))
  have hmne : m ≠ 1 := by
    intro hm
    rw [hm, mul_one] at hcomp
    exact hcomp hp
  have hm1 : 1 < m := lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hmne)
  have hs := prime_factor_square_le_local_gcd_quotient_mul hp.one_lt hm1
  rw [Nat.gcd_eq_left hdiv, Nat.div_self (Nat.sub_pos_of_lt hp.one_lt), one_mul] at hs
  exact hs

end PseudoPrime.PrimeTest
