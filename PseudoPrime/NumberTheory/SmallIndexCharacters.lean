/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CharacterKernelPowers
public import PseudoPrime.NumberTheory.QuadraticCrtKernels
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Character generators for index-four subgroups

Finite duality classifies every index-four subgroup at its original modulus as either a
single order-four character kernel or an intersection of two distinct quadratic kernels.
The result is independent of analytic kernels, weights, scales and numerical coefficients.
It supports finite quotient classification and conductor-family enumeration.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A commutative group of cardinality four has a generator or two distinct involutions.
Use the cyclic generator theorem in the first case. In the noncyclic case its exponent is
 two, and the cardinality supplies a second nonidentity element. This is a duality helper. -/
private theorem four_card_cases {G : Type*} [CommGroup G] [Fintype G] (hc : Fintype.card G = 4) :
    (∃ a : G, orderOf a = 4) ∨ ∃ a b : G, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b :=
  letI : DecidableEq G := Classical.decEq _
  letI : Decidable (IsCyclic G) := Classical.propDecidable _
  if hcyc : IsCyclic G then
    let _ : IsCyclic G := hcyc
    Or.inl
      (Exists.elim (IsCyclic.exists_generator (α := G)) fun a ha ↦
        ⟨a,
          (orderOf_eq_card_of_zpowers_eq_top ((Subgroup.eq_top_iff' _).mpr ha)).trans
            (Nat.card_eq_fintype_card.trans hc)⟩)
  else
    let hnat : Nat.card G = 4 := Nat.card_eq_fintype_card.trans hc
    let _ : Nontrivial G :=
      Finite.one_lt_card_iff_nontrivial.mp
        (hnat.symm ▸ Nat.le.step (Nat.le.step (show 2 ≤ 2 from Nat.le.refl)))
    let he :=
      (Monoid.exponent_eq_prime_iff Nat.prime_two).mp
        ((not_isCyclic_iff_exponent_eq_prime Nat.prime_two hnat).mp hcyc)
    Or.inr
      (Exists.elim (exists_prime_orderOf_dvd_card (G := G) 2 (hc.symm ▸ Nat.dvd_mul_right 2 2))
        fun a hao ↦
        let ha1 : a ≠ 1 := fun h ↦
          (Nat.succ_ne_self 1) (orderOf_one.symm.trans ((congrArg orderOf h).symm.trans hao)).symm
        let hpair : ({1, a} : Finset G).card = 2 := Finset.card_pair (Ne.symm ha1)
        let hu : (Finset.univ : Finset G).card = 4 := Finset.card_univ.trans hc
        Exists.elim
          (Finset.exists_mem_notMem_of_card_lt_card
            (hpair.symm ▸ hu.symm ▸ (show 2 < 4 from Nat.le.step (show 3 ≤ 3 from Nat.le.refl))))
          fun b hb ↦
          let hn := not_or.mp (Finset.mem_insert.not.mp hb.2)
          ⟨a, b, hao, he b hn.1, Ne.symm (fun h ↦ hn.2 (Finset.mem_singleton.mpr h))⟩)

/-- An index-four subgroup is cyclic-character or biquadratic-character defined.
Input: any subgroup at nonzero level with index four. Classify its finite annihilator,
transport character orders through the subtype, and identify kernels by their indices.
This gives same-modulus character inputs without assuming a CRT decomposition. -/
theorem index_four_character_cases {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) (hi : H.index = 4) :
    (∃ χ : DirichletCharacter ℂ q, orderOf χ = 4 ∧ H = χ.toUnitHom.ker) ∨
      ∃ a b : DirichletCharacter ℂ q,
        orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ H = a.toUnitHom.ker ⊓ b.toUnitHom.ker :=
  Or.elim (four_card_cases ((card_subgroupAnnihilator H).trans hi))
    (fun hc ↦
      Or.inl
        (Exists.elim hc fun χ ho ↦
          let hval := (orderOf_injective _ (subgroupAnnihilator H).subtype_injective χ).trans ho
          ⟨χ.val, hval, eq_kernel_of_order H χ.val χ.property (hval.trans hi.symm)⟩))
    (fun hc ↦
      Or.inr
        (Exists.elim hc fun a ha ↦
          Exists.elim ha fun b hb ↦
            let hao := (orderOf_injective _ (subgroupAnnihilator H).subtype_injective a).trans hb.1
            let hbo :=
              (orderOf_injective _ (subgroupAnnihilator H).subtype_injective b).trans hb.2.1
            let hab : a.val ≠ b.val := fun he ↦ hb.2.2 (Subtype.ext he)
            ⟨a.val, b.val, hao, hbo, hab,
              Subgroup.eq_of_index_dvd_index
                (le_inf (le_kernel_of_annihilator H a.val a.property)
                  (le_kernel_of_annihilator H b.val b.property))
                ((quadratic_kernel_inf_index a.val b.val hao hbo hab).trans hi.symm ▸
                  dvd_refl H.index)⟩))

end PseudoPrime.NumberTheory
