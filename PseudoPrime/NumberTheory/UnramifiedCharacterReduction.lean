/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.SubgroupAnnihilator

/-! # Unramified character reduction at a prime

Removing the prime-power part of the level identifies exactly the characters
with coprime conductor and turns their primitive prime values into unit values.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For a nonzero modulus and prime p, the image of characters from the
modulus with its p-power part removed is exactly the subgroup with conductor
coprime to p. Conductor invariance proves one inclusion; lifting the primitive
character proves the other. This identifies the unramified local character group. -/
theorem range_changeLevel_ordCompl {q p : ℕ} [NeZero q] (hp : p.Prime) :
    (DirichletCharacter.changeLevel (R := ℂ) (Nat.ordCompl_dvd q p)).range =
      DirichletCharacter.subgroupOfCoprimeConductor p := by
  let : NeZero (q / p ^ q.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne q)).ne'⟩
  ext χ
  change
    (∃ ψ, (DirichletCharacter.changeLevel (Nat.ordCompl_dvd q p)) ψ = χ) ↔ Nat.Coprime p χ.conductor
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [DirichletCharacter.conductor_changeLevel]
    exact (Nat.coprime_ordCompl hp (NeZero.ne q)).of_dvd_right ψ.conductor_dvd_level
  · intro hc
    have hd := Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level (hp.coprime_iff_not_dvd.mp hc)
    refine ⟨(DirichletCharacter.changeLevel hd) χ.primitiveCharacter, ?_⟩
    rw [← DirichletCharacter.changeLevel_trans, DirichletCharacter.changeLevel_primitiveCharacter]

/-- A character whose conductor is coprime to prime p lifts from the modulus
with its p-power part removed, and its primitive value at p equals the lifted
character value at the unit p. Use the image identity and primitive-level
invariance. This transfers local primitive evaluation to unit orthogonality. -/
theorem exists_lift_primitive_prime_value {q p : ℕ} [NeZero q] (hp : p.Prime)
    (χ : DirichletCharacter ℂ q) (hc : Nat.Coprime p χ.conductor) :
    ∃ ψ : DirichletCharacter ℂ (q / p ^ q.factorization p),
      (DirichletCharacter.changeLevel (Nat.ordCompl_dvd q p)) ψ = χ ∧
        ψ p = χ.primitiveCharacter p := by
  let : NeZero (q / p ^ q.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne q)).ne'⟩
  have hr : χ ∈ (DirichletCharacter.changeLevel (R := ℂ) (Nat.ordCompl_dvd q p)).range := by
    rw [range_changeLevel_ordCompl hp]
    exact hc
  obtain ⟨ψ, hψ⟩ := MonoidHom.mem_range.mp hr
  refine ⟨ψ, hψ, ?_⟩
  rw [← hψ]
  have he :=
    DirichletCharacter.primitiveCharacter_changeLevel_apply (Nat.ordCompl_dvd q p) ψ (p : ℤ)
  have hv :=
    ψ.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr (Nat.coprime_ordCompl hp (NeZero.ne q)))
  simpa only [Int.cast_natCast] using (he.trans hv).symm

/-- For characters with conductor coprime to prime p, primitive evaluation at p
preserves multiplication. Lift both characters to the modulus with its p-power
part removed, where p is a unit, and use level invariance and pointwise multiplication.
This supplies the local homomorphism used in unramified character orthogonality. -/
theorem primitive_prime_value_mul {q p : ℕ} [NeZero q] (hp : p.Prime) (χ ψ : DirichletCharacter ℂ q)
    (hc : Nat.Coprime p χ.conductor) (hd : Nat.Coprime p ψ.conductor) :
    (χ * ψ).primitiveCharacter p = χ.primitiveCharacter p * ψ.primitiveCharacter p := by
  let : NeZero (q / p ^ q.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne q)).ne'⟩
  obtain ⟨χ', hχ, hvχ⟩ := exists_lift_primitive_prime_value hp χ hc
  obtain ⟨ψ', hψ, hvψ⟩ := exists_lift_primitive_prime_value hp ψ hd
  have hmul : (DirichletCharacter.changeLevel (Nat.ordCompl_dvd q p)) (χ' * ψ') = χ * ψ := by
    rw [map_mul, hχ, hψ]
  rw [← hmul]
  have he :=
    DirichletCharacter.primitiveCharacter_changeLevel_apply (Nat.ordCompl_dvd q p) (χ' * ψ') (p : ℤ)
  have hv :=
    (χ' * ψ').primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr (Nat.coprime_ordCompl hp (NeZero.ne q)))
  simpa only [Int.cast_natCast, MulChar.mul_apply, hvχ, hvψ] using he.trans hv

/-- On a character subgroup with conductor coprime to prime p, primitive
evaluation at p defines a monoid homomorphism. The identity has conductor one,
and multiplicativity follows from reduction to the prime-free level.
This local homomorphism supplies the finite-group orthogonality argument. -/
private theorem exists_primitive_prime_value_hom {q p : ℕ} [NeZero q] (hp : p.Prime)
    (S : Subgroup (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, Nat.Coprime p χ.conductor) :
    ∃ f : S →* ℂ, ∀ χ : S, f χ = χ.val.primitiveCharacter p := by
  refine
    ⟨{  toFun := fun χ ↦ χ.val.primitiveCharacter p
        map_one' := ?_
        map_mul' := ?_ }, fun _ ↦ rfl⟩
  · rw [Subgroup.coe_one, DirichletCharacter.primitiveCharacter_one]
    apply MulChar.one_apply
    apply (ZMod.isUnit_iff_coprime p _).mpr
    rw [DirichletCharacter.conductor_one]
    exact Nat.coprime_one_right p
  · intro χ ψ
    rw [Subgroup.coe_mul]
    exact primitive_prime_value_mul hp χ.val ψ.val (hS χ.val χ.property) (hS ψ.val ψ.property)

/-- The real part of a complex monoid-homomorphism sum on a finite group is
nonnegative. A trivial homomorphism sums to the group cardinality; otherwise
translation by an element with value different from one forces the sum to zero.
This is the finite-group sign argument for unramified character values. -/
private theorem sum_monoidHom_re_nonneg {G : Type*} [Group G] [Fintype G] (f : G →* ℂ) :
    0 ≤ (∑ g : G, f g).re := by
  classical
  by_cases h : ∀ g : G, f g = 1
  · simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Complex.natCast_re]
    exact Nat.cast_nonneg _
  · obtain ⟨g, hg⟩ := not_forall.mp h
    have hs : f g * (∑ a : G, f a) = ∑ a : G, f a := by
      rw [Finset.mul_sum]
      exact
        Fintype.sum_bijective (fun a : G ↦ g * a) (Group.mulLeft_bijective g) (fun a ↦ f g * f a)
          (fun a ↦ f a) (fun a ↦ (map_mul f g a).symm)
    have hm : (f g - 1) * (∑ a : G, f a) = 0 := by rw [sub_mul, hs, one_mul, sub_self]
    have hz := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hg)
    rw [hz, Complex.zero_re]

/-- For a finite subgroup of characters with conductor coprime to prime p,
the real part of the sum of kth powers of primitive values at p is nonnegative.
Raise the local homomorphism to the kth power and use finite-group orthogonality.
This controls the unramified part of the primitive prime-power sum. -/
private theorem sum_unramified_primitive_prime_pow_re_nonneg {q p : ℕ} [NeZero q] (hp : p.Prime)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] (hS : ∀ χ ∈ S, Nat.Coprime p χ.conductor)
    (k : ℕ) : 0 ≤ (∑ χ : S, χ.val.primitiveCharacter p ^ k).re := by
  classical
  obtain ⟨f, hf⟩ := exists_primitive_prime_value_hom hp S hS
  let g : S →* ℂ :=
    { toFun := fun χ ↦ f χ ^ k
      map_one' := by rw [map_one, one_pow]
      map_mul' := fun χ ψ ↦ by rw [map_mul, mul_pow] }
  have h := sum_monoidHom_re_nonneg g
  simpa only [g, MonoidHom.coe_mk, OneHom.coe_mk, hf] using h

/-- For any finite character subgroup and positive exponent k, the sum of
primitive character values at p^k has nonnegative real part, for prime p.
Characters whose conductor is divisible by p contribute zero; the remaining
characters form the coprime-conductor intersection subgroup. Apply its local
homomorphism orthogonality. This supplies the sign of aggregate local Euler terms. -/
theorem sum_primitive_prime_pow_re_nonneg {q p : ℕ} [NeZero q] (hp : p.Prime)
    (S : Subgroup (DirichletCharacter ℂ q)) [Fintype S] {k : ℕ} (hk : 0 < k) :
    0 ≤ (∑ χ : S, χ.val.primitiveCharacter (p ^ k)).re := by
  classical
  simp only [map_pow]
  let U := S ⊓ DirichletCharacter.subgroupOfCoprimeConductor (R := ℂ) (n := q) p
  let : Fintype U := Fintype.ofFinite U
  let J := Finset.univ.filter (fun χ : S ↦ Nat.Coprime p χ.val.conductor)
  have hzero :
    ∑ χ ∈ J, χ.val.primitiveCharacter p ^ k = ∑ χ : S, χ.val.primitiveCharacter p ^ k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro χ hχ hχJ
    have hc : ¬Nat.Coprime p χ.val.conductor := by
      intro hc
      exact hχJ (Finset.mem_filter.mpr ⟨hχ, hc⟩)
    have hz : χ.val.primitiveCharacter p = 0 := by
      simpa only [Int.cast_natCast] using
        (DirichletCharacter.apply_eq_zero_iff χ.val.primitiveCharacter (p : ℤ)).mpr
          (by simpa only [Nat.isCoprime_iff_coprime] using hc)
    rw [hz, zero_pow hk.ne']
  have he : ∑ χ ∈ J, χ.val.primitiveCharacter p ^ k = ∑ χ : U, χ.val.primitiveCharacter p ^ k := by
    apply Finset.sum_bij (fun χ hχ ↦ (⟨χ.val, χ.property, (Finset.mem_filter.mp hχ).2⟩ : U))
    · intro χ hχ
      exact Finset.mem_univ _
    · intro χ hχ ψ hψ heq
      exact Subtype.ext (congrArg (fun ζ : U ↦ ζ.val) heq)
    · intro ψ _
      let χ : S := ⟨ψ.val, ψ.property.1⟩
      have hχ : χ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ψ.property.2⟩
      exact ⟨χ, hχ, rfl⟩
    · intro χ _
      rfl
  rw [← hzero, he]
  exact sum_unramified_primitive_prime_pow_re_nonneg hp U (fun χ hχ ↦ hχ.2) k

end PseudoPrime.NumberTheory
