/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CrtCharacters
/-! # Index four for independent quadratic character kernels -/

@[expose] public section

namespace PseudoPrime.NumberTheory
/-- Two distinct characters of exact order two have common unit kernel of
index four. Their annihilator contains the four distinct characters one,
a, b and a*b; the intersection index is at most the product of the two
individual indices. No cyclicity of the ambient unit group is assumed. -/
theorem quadratic_kernel_inf_index {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) :
    (a.toUnitHom.ker ⊓ b.toUnitHom.ker).index = 4 := by
  classical
  let H := a.toUnitHom.ker ⊓ b.toUnitHom.ker
  have hmem (χ : DirichletCharacter ℂ q) (hH : H ≤ χ.toUnitHom.ker) :
      χ ∈ subgroupAnnihilator H := by
    apply (mem_subgroupAnnihilator_iff H χ).mpr
    intro u hu
    have he := congrArg Units.val (MonoidHom.mem_ker.mp (hH hu))
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using he
  let A : subgroupAnnihilator H := ⟨a, hmem a inf_le_left⟩
  let B : subgroupAnnihilator H := ⟨b, hmem b inf_le_right⟩
  have ha0 : a ≠ 1 := by intro h; rw [h, orderOf_one] at ha; norm_num only at ha
  have hb0 : b ≠ 1 := by intro h; rw [h, orderOf_one] at hb; norm_num only at hb
  have hbi : b = b⁻¹ := eq_inv_iff_mul_eq_one.mpr
    (by rw [← pow_two, ← hb, pow_orderOf_eq_one])
  have hab0 : a * b ≠ 1 := by
    intro h
    exact hab ((eq_inv_iff_mul_eq_one.mpr h).trans hbi.symm)
  have hA : A ≠ 1 := fun h ↦ ha0 (congrArg Subtype.val h)
  have hB : B ≠ 1 := fun h ↦ hb0 (congrArg Subtype.val h)
  have hAB : A * B ≠ 1 := fun h ↦ hab0 (congrArg Subtype.val h)
  have hneq : A ≠ B := fun h ↦ hab (congrArg Subtype.val h)
  have hprodA : A ≠ A * B := by
    intro h
    apply hB
    exact mul_left_cancel (show A * B = A * 1 by rw [← h, mul_one])
  have hprodB : B ≠ A * B := by
    intro h
    apply hA
    exact mul_right_cancel (show A * B = 1 * B by rw [← h, one_mul])
  have hsub : ({1, A, B, A * B} : Finset (subgroupAnnihilator H)) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  have h1 : (1 : subgroupAnnihilator H) ∉ ({A, B, A * B} : Finset (subgroupAnnihilator H)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Ne.symm hA, Ne.symm hB,
      Ne.symm hAB, or_self, not_false_eq_true]
  have h2 : A ∉ ({B, A * B} : Finset (subgroupAnnihilator H)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, hneq, hprodA, or_self, not_false_eq_true]
  have h3 : B ∉ ({A * B} : Finset (subgroupAnnihilator H)) := by
    simpa only [Finset.mem_singleton] using hprodB
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton, Finset.card_univ,
    card_subgroupAnnihilator] at hcard
  have hu := Subgroup.index_inf_le (H := a.toUnitHom.ker) (K := b.toUnitHom.ker)
  rw [index_kernel_eq_order, index_kernel_eq_order, ha, hb] at hu
  exact le_antisymm hu hcard
/-- Primitive quadratic characters on coprime nonzero component levels,
with the second level greater than one, have lifted common kernel of index
four. Change of level preserves order and conductor; primitivity and
coprimality make the two lifted characters distinct. This supplies the
actual index for partial quadratic least-prime comparisons. -/
theorem quadratic_crt_kernel_index {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 2)
    (ha : α.IsPrimitive) (hb : β.IsPrimitive) (hmn : Nat.Coprime m n)
    (hn : 1 < n) :
    ((DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom.ker ⊓
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).toUnitHom.ker).index = 4 := by
  let a := DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α
  let b := DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
  have hca : a.conductor = m := (DirichletCharacter.conductor_changeLevel α _).trans ha
  have hcb : b.conductor = n := (DirichletCharacter.conductor_changeLevel β _).trans hb
  have hneq : a ≠ b := by
    intro he
    have hec := congrArg DirichletCharacter.conductor he
    rw [hca, hcb] at hec
    have hg := hmn.gcd_eq_one
    rw [hec, Nat.gcd_self] at hg
    omega
  have hao : orderOf a = 2 := (orderOf_injective
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
    (DirichletCharacter.changeLevel_injective _) α).trans hα
  have hbo : orderOf b = 2 := (orderOf_injective
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
    (DirichletCharacter.changeLevel_injective _) β).trans hβ
  exact quadratic_kernel_inf_index a b hao hbo hneq
end PseudoPrime.NumberTheory
