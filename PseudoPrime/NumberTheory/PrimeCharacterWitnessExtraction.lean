/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Data.Nat.Factors

/-! # Prime extraction from nontrivial multiplicative integer witnesses -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- If a positive integer maps to a value different from one under a monoid
homomorphism, a prime divisor also maps to a value different from one.
Factor the integer and extract a non-one factor of the mapped product.
The extracted prime is at most the original integer. -/
theorem exists_prime_divisor_map_ne_one {M : Type*} [Monoid M] (f : ℕ →* M) {a : ℕ} (ha : 0 < a)
    (hne : f a ≠ 1) : ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ≤ a ∧ f p ≠ 1 := by
  have hprod : (a.primeFactorsList.map f).prod ≠ 1 := by
    rw [← f.map_list_prod, Nat.prod_primeFactorsList ha.ne']
    exact hne
  obtain ⟨v, hv, hv1⟩ := List.exists_mem_ne_one_of_prod_ne_one hprod
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  have hd := (Nat.mem_primeFactorsList ha.ne').mp hp
  exact ⟨p, hd.1, hd.2, Nat.le_of_dvd ha hd.2, hv1⟩

/-- If the original multiplicative value is also nonzero, the extracted
prime value is nonzero. Multiplicativity and zero absorption preserve this
condition. This prevents replacing a unit nonresidue by a zero-value divisor. -/
theorem exists_prime_divisor_map_nonzero_ne_one {M : Type*} [MonoidWithZero M] (f : ℕ →* M) {a : ℕ}
    (ha : 0 < a) (hz : f a ≠ 0) (hne : f a ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ≤ a ∧ f p ≠ 0 ∧ f p ≠ 1 := by
  obtain ⟨p, hp, hd, hpa, hp1⟩ := exists_prime_divisor_map_ne_one f ha hne
  have hp0 : f p ≠ 0 := by
    intro h
    apply hz
    obtain ⟨m, hm⟩ := hd
    rw [hm, map_mul, h, zero_mul]
  exact ⟨p, hp, hd, hpa, hp0, hp1⟩

/-- For any Dirichlet character, a positive nonzero non-one integer value
gives a prime divisor with the same two exclusions and no larger size.
The extracted prime is coprime to the modulus. No quadraticity, primitivity,
nonprincipality or analytic hypothesis is needed beyond the witness itself. -/
theorem exists_prime_divisor_character_nonzero_ne_one {R : Type*} [CommMonoidWithZero R]
    [Nontrivial R] {q a : ℕ} (χ : DirichletCharacter R q) (ha : 0 < a) (hz : χ (a : ZMod q) ≠ 0)
    (hne : χ (a : ZMod q) ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ p ≤ a ∧ p.Coprime q ∧ χ (p : ZMod q) ≠ 0 ∧ χ (p : ZMod q) ≠ 1 := by
  let f : ℕ →* R := χ.toMonoidHom.comp (Nat.castRingHom (ZMod q)).toMonoidHom
  obtain ⟨p, hp, hd, hpa, hp0, hp1⟩ := exists_prime_divisor_map_nonzero_ne_one f ha hz hne
  have hunit : IsUnit (p : ZMod q) := MulChar.apply_ne_zero_iff.mp hp0
  exact ⟨p, hp, hd, hpa, (ZMod.isUnit_iff_coprime p q).mp hunit, hp0, hp1⟩

/-- A least positive integer on which a Dirichlet character is nonzero and
different from one is prime. Extract a prime divisor and use minimality.
This justifies passing from an integer nonresidue theorem to a prime witness
without a quadraticity restriction or a loss in the upper bound. -/
theorem prime_of_least_character_nonzero_ne_one {R : Type*} [CommMonoidWithZero R] [Nontrivial R]
    {q a : ℕ} (χ : DirichletCharacter R q) (ha : 0 < a) (hz : χ (a : ZMod q) ≠ 0)
    (hne : χ (a : ZMod q) ≠ 1)
    (hmin : ∀ b : ℕ, 0 < b → b < a → χ (b : ZMod q) = 0 ∨ χ (b : ZMod q) = 1) : a.Prime := by
  obtain ⟨p, hp, _, hpa, _, hp0, hp1⟩ := exists_prime_divisor_character_nonzero_ne_one χ ha hz hne
  have hnot : ¬p < a := by
    intro hlt
    exact (hmin p hp.pos hlt).elim hp0 hp1
  have he : p = a := le_antisymm hpa (Nat.le_of_not_gt hnot)
  exact he ▸ hp

end PseudoPrime.NumberTheory
