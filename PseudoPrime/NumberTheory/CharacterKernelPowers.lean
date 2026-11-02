/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CharacterKernelOrder

/-! # Conductors of coprime powers and characters of prime-index quotients

These identities concern arbitrary character orders and subgroup indices. They support
finite character duality and conductor enumeration independently of any analytic kernel
or chosen prime-bound coefficient. Application-specific families are kept in their consumers.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A power coprime to a character's order preserves its conductor.
Input: any complex character and a coprime exponent. Both powers generate the same cyclic
subgroup; recover the original character as a power and apply conductor divisibility twice.
This supplies conductor identities for finite character-family enumeration. -/
theorem conductor_pow_coprime {q : ℕ} (χ : DirichletCharacter ℂ q) {k : ℕ}
    (hk : k.Coprime (orderOf χ)) : (χ ^ k).conductor = χ.conductor :=
  Nat.dvd_antisymm (χ.conductor_pow_dvd k)
    (Exists.elim (exists_pow_eq_self_of_coprime hk) fun m hm ↦
      (congrArg DirichletCharacter.conductor hm) ▸ ((χ ^ k).conductor_pow_dvd m))

/-- An annihilator member vanishes on the original subgroup.
Input: a subgroup and a character in its annihilator. The conclusion is subgroup containment
in the unit kernel. Convert the defining character equality into equality of units.
This connects finite duality to subgroup-kernel arguments. -/
theorem le_kernel_of_annihilator {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ∈ subgroupAnnihilator H) : H ≤ χ.toUnitHom.ker :=
  fun u hu ↦
  MonoidHom.mem_ker.mpr
    (Units.ext ((MulChar.coe_toUnitHom χ u).trans ((mem_subgroupAnnihilator_iff H χ).mp hχ u hu)))

/-- An annihilator character whose order equals the subgroup index has exactly that kernel.
Input: annihilator membership and matching order. Containment and equal finite indices force
equality. This recovers a subgroup from a generating dual character. -/
theorem eq_kernel_of_order {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q)
    (hχ : χ ∈ subgroupAnnihilator H) (ho : orderOf χ = H.index) : H = χ.toUnitHom.ker :=
  Subgroup.eq_of_index_dvd_index (le_kernel_of_annihilator H χ hχ)
    ((index_kernel_eq_order χ).trans ho ▸ dvd_refl H.index)

/-- Every prime-index subgroup is the unit kernel of a character of that prime order.
Input: a subgroup at nonzero level and its prime index. Apply Cauchy's theorem to the finite
annihilator, then use equal indices. This gives character generators for prime quotients. -/
theorem prime_index_kernel {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {p : ℕ} [Fact p.Prime]
    (hi : H.index = p) : ∃ χ : DirichletCharacter ℂ q, orderOf χ = p ∧ H = χ.toUnitHom.ker :=
  Exists.elim
    (exists_prime_orderOf_dvd_card (G := subgroupAnnihilator H) p
      ((card_subgroupAnnihilator H).trans hi ▸ dvd_refl p))
    fun χ ho ↦
    ⟨χ.val, (orderOf_injective _ (subgroupAnnihilator H).subtype_injective χ).trans ho,
      eq_kernel_of_order H χ.val χ.property
        (((orderOf_injective _ (subgroupAnnihilator H).subtype_injective χ).trans ho).trans
          hi.symm)⟩

/-- A subgroup whose index is a product of coprime primes is a character kernel.
Input: two prime factors, their coprimality, and the subgroup index. Cauchy's theorem gives
commuting annihilator elements of the two orders; their product has the full index.
The equal-index kernel identity gives a generator for this squarefree dual quotient. -/
theorem coprime_prime_index_kernel {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hpr : p.Coprime r) (hi : H.index = p * r) :
    ∃ χ : DirichletCharacter ℂ q, orderOf χ = p * r ∧ H = χ.toUnitHom.ker :=
  let ha :=
    exists_prime_orderOf_dvd_card (G := subgroupAnnihilator H) p
      ((card_subgroupAnnihilator H).trans hi ▸ Nat.dvd_mul_right p r)
  let hb :=
    exists_prime_orderOf_dvd_card (G := subgroupAnnihilator H) r
      ((card_subgroupAnnihilator H).trans hi ▸ Nat.dvd_mul_left r p)
  Exists.elim ha fun a hao ↦
    Exists.elim hb fun b hbo ↦
      let ho : orderOf (a * b) = p * r :=
        ((Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime (hao.symm ▸ hbo.symm ▸ hpr)).trans
          (congrArg₂ (fun u v : ℕ ↦ u * v) hao hbo)
      let hval := (orderOf_injective _ (subgroupAnnihilator H).subtype_injective (a * b)).trans ho
      ⟨(a * b).val, hval, eq_kernel_of_order H (a * b).val (a * b).property (hval.trans hi.symm)⟩

end PseudoPrime.NumberTheory
