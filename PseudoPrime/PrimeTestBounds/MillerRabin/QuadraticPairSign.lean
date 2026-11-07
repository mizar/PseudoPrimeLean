/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.PairedQuadraticAnnihilator
public import PseudoPrime.PrimeTest.MillerRabin.KorseltCanonicalSign

/-! # Pair-level character triviality on the common-sign subgroup -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At two odd prime divisors, the original pair-level Jacobi character is one
on a representative of a common-sign unit when the exponent is an odd multiple
of each local half exponent. Transfer the paired Legendre identity through
Jacobi multiplicativity. This preserves the pair level for the Euler comparison. -/
theorem pair_character_eq_one_on_sign {n p q E kp kq : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hpq : Odd (p * q)) (hpn : p ∣ n)
    (hqn : q ∣ n) (hkp : Odd kp) (hkq : Odd kq) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq)
    (u : (ZMod n)ˣ) (hu : u ∈ PseudoPrime.PrimeTest.signSubgroup n E) :
    PseudoPrime.NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq
        (((u : ZMod n).val : ℕ) : ZMod (p * q)) =
      1 := by
  have h :=
    PseudoPrime.PrimeTest.legendre_pair_mul_eq_one_on_signSubgroup hpn hqn hkp hkq hEp hEq u hu
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym] at h
  have he :=
    PseudoPrime.NumberTheory.complexJacobiNumeratorCharacter_apply_int (p * q) hpq
      (((u : ZMod n).val : ℕ) : ℤ)
  rw [jacobiSym.mul_right, h, Int.cast_one, Int.cast_natCast] at he
  exact he

/-- For two odd prime divisors satisfying Korselt divisibility and equal
predecessor valuations, a strong MR pass has pair-character value one on its
canonical representative. Construct the common sign exponent internally.
This connects MR passes to pair-level character triviality. -/
theorem pair_character_eq_one_of_strongPass {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hpn : p ∣ n) (hqn : q ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1)) {x : ZMod n}
    (hx : PrimeTest.StrongMillerRabinPass n x) :
    NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq) (x.val : ZMod (p * q)) =
      1 := by
  obtain ⟨kp, hkp, hEp⟩ :=
    PrimeTest.canonical_sign_exponent_local_half (Fact.out : p.Prime).one_lt hp hn ho hpk
  obtain ⟨kq, hkq, hEq⟩ :=
    PrimeTest.canonical_sign_exponent_local_half (Fact.out : q.Prime).one_lt hq hn ho hqk
  rw [hv] at hEq
  obtain ⟨u, hu, huval⟩ :=
    PrimeTest.strongMillerRabinPass_mem_signSubgroup hn ho hx (Fact.out : p.Prime) hp hpn
  have he := pair_character_eq_one_on_sign (hp.mul hq) hpn hqn hkp hkq hEp hEq u hu
  rw [huval] at he
  exact he

/-- Under the two-prime Korselt and valuation conditions, a natural strong
MR pass has original pair-level character value one when the pair divides the
ambient modulus. Transport the canonical representative through the reduction
map. This gives the small-prime triviality used by the Euler prefix theorem. -/
theorem pair_character_nat_eq_one {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q)
    (hpn : p ∣ n) (hqn : q ∣ n) (hpqn : p * q ∣ n) (hpk : p - 1 ∣ n - 1) (hqk : q - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1)) (k : ℕ)
    (hk : PrimeTest.StrongMillerRabinPass n (k : ZMod n)) :
    NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq) k = 1 := by
  have he := pair_character_eq_one_of_strongPass hn ho hp hq hpn hqn hpk hqk hv hk
  have hvk : (((k : ZMod n).val : ℕ) : ZMod (p * q)) = (k : ZMod (p * q)) :=
    (ZMod.cast_eq_val (R := ZMod (p * q)) (k : ZMod n)).symm.trans (ZMod.cast_natCast hpqn k)
  rw [hvk] at he
  exact he

/-- An odd pair level congruent to one modulo four has even Jacobi
character. Evaluate at minus one using the supplementary law. This supplies
the parity needed by the even Gamma resolvent comparison. -/
theorem pair_character_even {p q : ℕ} (hpq : Odd (p * q)) (hmod : (p * q) % 4 = 1) :
    (NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq).Even := by
  change NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq (-1 : ZMod (p * q)) = 1
  have h := NumberTheory.complexJacobiNumeratorCharacter_apply_int (p * q) hpq (-1)
  rw [jacobiSym.at_neg_one hpq, ZMod.χ₄_nat_one_mod_four hmod] at h
  simpa only [Int.cast_neg, Int.cast_one] using h

/-- A pair dividing a squarefree ambient modulus has primitive original
Jacobi character at its odd pair level. Squarefreeness descends along the
divisibility relation, so the existing exact-conductor theorem applies.
This supplies primitivity without an external character classification. -/
theorem pair_character_primitive {n p q : ℕ} (hn : Squarefree n) (hpqn : p * q ∣ n)
    (hpq : Odd (p * q)) : (NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq).IsPrimitive :=
  NumberTheory.complexJacobiNumeratorCharacter_isPrimitive _ hpq (hn.squarefree_of_dvd hpqn)

/-- A shared sign exponent that is an odd multiple of each local half
exponent forces the original pair character to be even. The negative unit
belongs to every sign subgroup, so evaluate its paired character there.
This avoids a separate residue-class premise in the analytic branch. -/
theorem pair_character_even_of_sign {p q E kp kq : ℕ} [NeZero (p * q)] [NeZero p] [NeZero q]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hpq : Odd (p * q)) (hkp : Odd kp)
    (hkq : Odd kq) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) :
    (NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq).Even := by
  have hu : (-1 : (ZMod (p * q))ˣ) ∈ PrimeTest.signSubgroup (p * q) E := neg_one_pow_eq_or _ E
  have he :=
    pair_character_eq_one_on_sign hpq (dvd_mul_right p q) (dvd_mul_left q p) hkp hkq hEp hEq (-1) hu
  change NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq (-1 : ZMod (p * q)) = 1
  simpa only [Units.val_neg, Units.val_one, ZMod.natCast_zmod_val] using he

/-- Korselt divisibility for two odd primes and equality of their
predecessor valuations make their original pair character even. Construct
the two local odd half-exponent factors using the ambient odd part and
evaluate the negative unit in the resulting common-sign subgroup.
This discharges parity from the arithmetic hypotheses of the U branch. -/
theorem pair_character_even_of_korselt {n p q : ℕ} [NeZero p] [NeZero q] [NeZero (p * q)]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hpk : p - 1 ∣ n - 1) (hqk : q - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1)) :
    (NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)).Even := by
  obtain ⟨kp, hkp, hEp⟩ :=
    PrimeTest.canonical_sign_exponent_local_half (Fact.out : p.Prime).one_lt hp hn ho hpk
  obtain ⟨kq, hkq, hEq⟩ :=
    PrimeTest.canonical_sign_exponent_local_half (Fact.out : q.Prime).one_lt hq hn ho hqk
  rw [hv] at hEq
  exact pair_character_even_of_sign (hp.mul hq) hkp hkq hEp hEq

/-- The original odd pair character is nonprincipal when its level divides
a squarefree modulus and exceeds one. Primitivity identifies its conductor
with the pair level, whereas the principal character has conductor one.
This supplies the nonprincipal hypothesis of the Gamma comparison. -/
theorem pair_character_ne_one {n p q : ℕ} (hn : Squarefree n) (hpqn : p * q ∣ n) (hpq : Odd (p * q))
    (hprod : 1 < p * q) : NumberTheory.complexJacobiNumeratorCharacter (p * q) hpq ≠ 1 := by
  let : NeZero (p * q) := ⟨(Nat.zero_lt_of_lt hprod).ne'⟩
  have hprim := pair_character_primitive hn hpqn hpq
  intro he
  have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
  exact (Nat.ne_of_gt hprod) (hprim.symm.trans hcond)

end PseudoPrime.PrimeTestBounds.MillerRabin
