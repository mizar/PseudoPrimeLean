/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitPowerCardinality
public import Mathlib.Data.Nat.Factorization.Induction

/-! # Lower bounds and common negative fibers for modular power images -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For an odd prime power, an exponent with smaller two-adic valuation than p-1
has an even power-image cardinality. The totient has the same two-adic valuation
as p-1, and its quotient by the kernel gcd retains a factor two.
This supplies the local even-image condition in global MR subgroup estimates. -/
theorem two_dvd_card_unitPowerImage_prime_pow {p a E : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a)
    (hE : E ≠ 0) (hv : padicValNat 2 E < padicValNat 2 (p - 1)) :
    2 ∣ Nat.card (powMonoidHom E : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).range := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let : IsCyclic (ZMod (p ^ a))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 a
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  apply two_dvd_div_gcd_of_twoAdic_lt hE
  rw [Nat.totient_prime_pow hp ha,
    padicValNat.mul (pow_ne_zero _ hp.ne_zero) (Nat.sub_ne_zero_of_lt hp.one_lt),
    padicValNat.eq_zero_of_not_dvd (hp.odd_of_ne_two hp2).pow.not_two_dvd_nat, Nat.zero_add]
  exact hv

/-- An even power image modulo an odd prime power contains -1. The unit group is
cyclic and its signs are distinct, so the order-two subgroup lies in the image.
This produces a negative fiber which can be combined with other CRT factors. -/
theorem exists_unit_pow_eq_neg_one_prime_pow_of_even_image {p a E : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (he : 2 ∣ Nat.card (powMonoidHom E : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).range) :
    ∃ u : (ZMod (p ^ a))ˣ, u ^ E = -1 := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let : IsCyclic (ZMod (p ^ a))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 a
  have hgt : 2 < p ^ a :=
    lt_of_lt_of_le (lt_of_le_of_ne hp.two_le hp2.symm) (Nat.le_self_pow ha.ne' p)
  let : Fact (2 < p ^ a) := ⟨hgt⟩
  apply
    exists_unit_pow_eq_neg_one_of_even_image
      (fun h ↦ ZMod.neg_one_ne_one (n := p ^ a) (congrArg Units.val h))
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at he
  exact he

/-- If p does not divide E and E has smaller two-adic valuation than p-1, the
E-power image modulo p^a has at least 2*p^(a-1) elements. Its prime-power factor
survives in the exact cardinality formula and its remaining quotient is even.
This excludes small image sizes at repeated prime factors. -/
theorem two_mul_primePower_le_card_unitPowerImage {p a E : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hE : E ≠ 0) (hpE : ¬p ∣ E) (hv : padicValNat 2 E < padicValNat 2 (p - 1)) :
    2 * p ^ (a - 1) ≤ Nat.card (powMonoidHom E : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).range := by
  rw [card_unitPowerImage_prime_pow_of_not_dvd hp hp2 ha hpE, Nat.mul_comm 2]
  apply Nat.mul_le_mul_left
  apply Nat.le_of_dvd
  · exact
      Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) (Nat.gcd_dvd_left (p - 1) E))
        (Nat.gcd_pos_of_pos_left E (Nat.sub_pos_of_lt hp.one_lt))
  · exact two_dvd_div_gcd_of_twoAdic_lt hE hv

/-- For an odd modulus n>1 and nonzero E, if E has smaller two-adic valuation
than p-1 at every prime divisor, -1 has a global E-power preimage and the image
cardinality is even. Induct on prime powers and coprime products, preserving
one common negative sign through CRT. This supplies the global two-fiber count. -/
theorem exists_negative_root_and_even_image_of_local_twoAdic_lt {n E : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hE : E ≠ 0)
    (hv : ∀ p : ℕ, p.Prime → p ∣ n → padicValNat 2 E < padicValNat 2 (p - 1)) :
    (∃ u : (ZMod n)ˣ, u ^ E = -1) ∧
      2 ∣ Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range := by
  revert hn1 hnOdd hv
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    intro hn _ _
    exact ((not_lt_of_ge (by decide : 0 ≤ 1)) hn).elim
  | prime_pow p a hp =>
    intro hn ho hv
    have ha : 0 < a :=
      Nat.pos_of_ne_zero fun h ↦ by
        rw [h, pow_zero] at hn
        exact (lt_irrefl 1) hn
    have hpd : p ∣ p ^ a := dvd_pow_self p ha.ne'
    have hp2 := ho.ne_two_of_dvd_nat hpd
    have he := two_dvd_card_unitPowerImage_prime_pow hp hp2 ha hE (hv p hp hpd)
    exact ⟨exists_unit_pow_eq_neg_one_prime_pow_of_even_image hp hp2 ha he, he⟩
  | coprime m n hm hn hc ihm ihn =>
    intro _ ho hv
    let : NeZero m := ⟨Nat.ne_zero_of_lt hm⟩
    let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
    obtain ⟨hrootm, hem⟩ :=
      ihm hm (Nat.odd_mul.mp ho).1 (fun p hp hd ↦ hv p hp (hd.trans (dvd_mul_right m n)))
    obtain ⟨hrootn, _⟩ :=
      ihn hn (Nat.odd_mul.mp ho).2 (fun p hp hd ↦ hv p hp (hd.trans (dvd_mul_left n m)))
    refine ⟨exists_unit_pow_eq_neg_one_coprime_mul hc hrootm hrootn, ?_⟩
    rw [card_unitPowerImage_coprime_mul hc]
    exact dvd_mul_of_dvd_left hem _

/-- For odd n>1 and nonzero E, if every prime factor is coprime to E and has
larger local two-adic valuation, a power image with fewer than four elements
forces n to be prime. Repeated prime factors give at least six image elements,
and a coprime product gives at least four. This isolates the smallest image case. -/
theorem prime_of_card_unitPowerImage_lt_four {n E : ℕ} (hn1 : 1 < n) (hnOdd : Odd n) (hE : E ≠ 0)
    (hpE : ∀ p : ℕ, p.Prime → p ∣ n → ¬p ∣ E)
    (hv : ∀ p : ℕ, p.Prime → p ∣ n → padicValNat 2 E < padicValNat 2 (p - 1))
    (hsmall : Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range < 4) : n.Prime := by
  revert hn1 hnOdd hpE hv hsmall
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    intro hn _ _ _ _
    exact ((not_lt_of_ge (by decide : 0 ≤ 1)) hn).elim
  | prime_pow p a hp =>
    intro hn ho hpE hv hsmall
    have ha : 0 < a :=
      Nat.pos_of_ne_zero fun h ↦ by
        rw [h, pow_zero] at hn
        exact (lt_irrefl 1) hn
    have hpd : p ∣ p ^ a := dvd_pow_self p ha.ne'
    have hp2 := ho.ne_two_of_dvd_nat hpd
    have hlo := two_mul_primePower_le_card_unitPowerImage hp hp2 ha hE (hpE p hp hpd) (hv p hp hpd)
    by_cases ha1 : a = 1
    · rw [ha1, pow_one]
      exact hp
    have ha2 : 2 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne ha (Ne.symm ha1))
    have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le hp2.symm)
    have hex : 1 ≤ a - 1 := Nat.sub_le_sub_right ha2 1
    have hpow : 3 ≤ p ^ (a - 1) := hp3.trans (Nat.le_self_pow (Nat.ne_zero_of_lt hex) p)
    exact (by linarith only [hpow, hlo, hsmall] : False).elim
  | coprime m n hm hn hc _ _ =>
    intro _ ho _ hv hsmall
    let : NeZero m := ⟨Nat.ne_zero_of_lt hm⟩
    let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
    have hem :=
      (exists_negative_root_and_even_image_of_local_twoAdic_lt hm (Nat.odd_mul.mp ho).1 hE
          (fun p hp hd ↦ hv p hp (hd.trans (dvd_mul_right m n)))).2
    have hen :=
      (exists_negative_root_and_even_image_of_local_twoAdic_lt hn (Nat.odd_mul.mp ho).2 hE
          (fun p hp hd ↦ hv p hp (hd.trans (dvd_mul_left n m)))).2
    rw [card_unitPowerImage_coprime_mul hc] at hsmall
    have h4 := Nat.mul_le_mul (Nat.le_of_dvd Nat.card_pos hem) (Nat.le_of_dvd Nat.card_pos hen)
    exact ((not_lt_of_ge h4) hsmall).elim

/-- Under the local coprimality and two-adic conditions, an odd prime power
with fewer than eight image elements is a prime or 9. The surviving p^(a-1)
factor leaves only 3^2 among composite prime powers. This handles the exceptional
local branch in the general small-image classification. -/
private theorem prime_or_nine_of_card_unitPowerImage_prime_pow_lt_eight {p a E : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hE : E ≠ 0) (hpE : ¬p ∣ E)
    (hv : padicValNat 2 E < padicValNat 2 (p - 1))
    (hsmall : Nat.card (powMonoidHom E : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).range < 8) :
    (p ^ a).Prime ∨ p ^ a = 9 := by
  by_cases ha1 : a = 1
  · rw [ha1, pow_one]
    exact Or.inl hp
  have ha2 : 2 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne ha (Ne.symm ha1))
  have hlo := two_mul_primePower_le_card_unitPowerImage hp hp2 ha hE hpE hv
  have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le hp2.symm)
  by_cases hpEq : p = 3
  · by_cases haEq : a = 2
    · exact
        Or.inr
          (by
            rw [hpEq, haEq]; rfl)
    have ha3 : 3 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne ha2 (Ne.symm haEq))
    have h9 := Nat.pow_le_pow_right hp.pos (Nat.sub_le_sub_right ha3 1)
    rw [hpEq] at h9
    rw [hpEq] at hlo hsmall
    have hc : 9 ≤ 3 ^ (a - 1) := h9
    exact (by linarith only [hc, hlo, hsmall] : False).elim
  · have hp4 : 4 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp3 (Ne.symm hpEq))
    have hex : 1 ≤ a - 1 := Nat.sub_le_sub_right ha2 1
    have hpow : 4 ≤ p ^ (a - 1) := hp4.trans (Nat.le_self_pow (Nat.ne_zero_of_lt hex) p)
    exact (by linarith only [hpow, hlo, hsmall] : False).elim

/-- For odd n>1 and nonzero E, local coprimality and strictly smaller two-adic
valuation imply that a power image with fewer than eight elements occurs only
at a prime, at 9, or at a product of two distinct primes. In a coprime product
both images must have fewer than four elements and hence prime moduli.
This reduces the remaining low-index MR case to the two-prime divisibility contradiction. -/
theorem prime_or_nine_or_two_primes_of_card_unitPowerImage_lt_eight {n E : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hE : E ≠ 0) (hpE : ∀ p : ℕ, p.Prime → p ∣ n → ¬p ∣ E)
    (hv : ∀ p : ℕ, p.Prime → p ∣ n → padicValNat 2 E < padicValNat 2 (p - 1))
    (hsmall : Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range < 8) :
    n.Prime ∨ n = 9 ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q := by
  revert hn1 hnOdd hpE hv hsmall
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    intro hn _ _ _ _
    exact ((not_lt_of_ge (by decide : 0 ≤ 1)) hn).elim
  | prime_pow p a hp =>
    intro hn ho hpE hv hsmall
    have ha : 0 < a :=
      Nat.pos_of_ne_zero fun h ↦ by
        rw [h, pow_zero] at hn
        exact (lt_irrefl 1) hn
    have hpd : p ∣ p ^ a := dvd_pow_self p ha.ne'
    have hclass :=
      prime_or_nine_of_card_unitPowerImage_prime_pow_lt_eight hp (ho.ne_two_of_dvd_nat hpd) ha hE
        (hpE p hp hpd) (hv p hp hpd) hsmall
    exact hclass.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  | coprime m n hm hn hc _ _ =>
    intro _ ho hpE hv hsmall
    let : NeZero m := ⟨Nat.ne_zero_of_lt hm⟩
    let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
    have hvm := fun (p : ℕ) (hp : p.Prime) (hd : p ∣ m) ↦ hv p hp (hd.trans (dvd_mul_right m n))
    have hvn := fun (p : ℕ) (hp : p.Prime) (hd : p ∣ n) ↦ hv p hp (hd.trans (dvd_mul_left n m))
    have hem :=
      (exists_negative_root_and_even_image_of_local_twoAdic_lt hm (Nat.odd_mul.mp ho).1 hE hvm).2
    have hen :=
      (exists_negative_root_and_even_image_of_local_twoAdic_lt hn (Nat.odd_mul.mp ho).2 hE hvn).2
    have hA := Nat.le_of_dvd Nat.card_pos hem
    have hB := Nat.le_of_dvd Nat.card_pos hen
    rw [card_unitPowerImage_coprime_mul hc] at hsmall
    have hAm : Nat.card (powMonoidHom E : (ZMod m)ˣ →* (ZMod m)ˣ).range < 4 := by
      by_contra h
      have h8 := Nat.mul_le_mul (le_of_not_gt h) hB
      exact (not_lt_of_ge h8) hsmall
    have hBn : Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range < 4 := by
      by_contra h
      have h8 := Nat.mul_le_mul hA (le_of_not_gt h)
      exact (not_lt_of_ge h8) hsmall
    have hmp :=
      prime_of_card_unitPowerImage_lt_four hm (Nat.odd_mul.mp ho).1 hE
        (fun p hp hd ↦ hpE p hp (hd.trans (dvd_mul_right m n))) hvm hAm
    have hnp :=
      prime_of_card_unitPowerImage_lt_four hn (Nat.odd_mul.mp ho).2 hE
        (fun p hp hd ↦ hpE p hp (hd.trans (dvd_mul_left n m))) hvn hBn
    have hne : m ≠ n := by
      intro h
      rw [← h, Nat.coprime_self] at hc
      exact hm.ne' hc
    exact Or.inr (Or.inr ⟨m, n, hmp, hnp, hne, rfl⟩)

end PseudoPrime.NumberTheory
