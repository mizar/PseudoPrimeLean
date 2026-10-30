/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.CharacterKernelOrder

/-! # Independent quadratic and cubic CRT characters -/

@[expose] public section
namespace PseudoPrime.NumberTheory
/-- The product at level m*n of the two characters pulled back along its
projections to levels m and n. Changing levels gives the CRT pullbacks on units.
The order-two and order-three hypotheses below guarantee an independent product. -/
noncomputable def crtCharacter {m n : ℕ} (α : DirichletCharacter ℂ m)
    (β : DirichletCharacter ℂ n) : DirichletCharacter ℂ (m * n) :=
  DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α *
    DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
/-- For characters of exact orders two and three at nonzero levels, the CRT
product has exact order six. Change of level is injective, and commuting elements
of coprime orders have product order equal to the product. No cyclic-unit assumption is used. -/
theorem crtCharacter_order {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) : orderOf (crtCharacter α β) = 6 := by
  have ha := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
    (DirichletCharacter.changeLevel_injective _) α
  have hb := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
    (DirichletCharacter.changeLevel_injective _) β
  have hc : Nat.Coprime
      (orderOf (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α))
      (orderOf (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β)) := by
    rw [ha,hb,hα,hβ];norm_num only
  rw [crtCharacter,(Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hc,ha,hb,hα,hβ]

/-- The k-th power of the CRT character splits into the left power modulo two
and the right power modulo three. Preserve orders under change of level and reduce
each exponent. This computes the five nonprincipal conductor contributions. -/
theorem crtCharacter_powers {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (k : ℕ) :
    (crtCharacter α β) ^ k =
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α) ^ (k % 2) *
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β) ^ (k % 3) := by
  have ha := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
    (DirichletCharacter.changeLevel_injective _) α
  have hb := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
    (DirichletCharacter.changeLevel_injective _) β
  rw [hα] at ha
  rw [hβ] at hb
  rw [crtCharacter,mul_pow,← pow_mod_orderOf _ k,ha,← pow_mod_orderOf
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β) k,hb]
/-- A relation between natural powers of the two lifted characters is trivial
only when the exponents are divisible by two and three respectively. The orders of
the powers remain coprime, so a product equal to one forces both powers to be one.
This proves the independence required by the CRT subgroup construction. -/
theorem crtCharacter_independent {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (i j : ℕ)
    (he : (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α) ^ i *
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β) ^ j = 1) :
    2 ∣ i ∧ 3 ∣ j := by
  have ha := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n))
    (DirichletCharacter.changeLevel_injective _) α
  have hb := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
    (DirichletCharacter.changeLevel_injective _) β
  rw [hα] at ha
  rw [hβ] at hb
  have hc : Nat.Coprime
      (orderOf (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α))
      (orderOf (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β)) := by
    rw [ha,hb];norm_num only
  have hcp := Nat.Coprime.of_dvd_right (orderOf_pow_dvd j)
    (Nat.Coprime.of_dvd_left (orderOf_pow_dvd i) hc)
  have hprod := (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime hcp
  rw [he,orderOf_one] at hprod
  have ho1 := Nat.dvd_one.mp ⟨_,hprod⟩
  have ho2 := Nat.dvd_one.mp ⟨_,hprod.trans (mul_comm _ _)⟩
  constructor
  · rw [← ha]
    exact orderOf_dvd_iff_pow_eq_one.mpr (orderOf_eq_one_iff.mp ho1)
  · rw [← hb]
    exact orderOf_dvd_iff_pow_eq_one.mpr (orderOf_eq_one_iff.mp ho2)

/-- For coprime levels and exact orders two and three, the five nonprincipal
powers have conductors f2*f3,f3,f2,f3,f2*f3. Apply the coprime conductor product
formula, invariance under change of level and invariance under inversion. -/
theorem crtCharacter_conductors {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) (hmn : Nat.Coprime m n) :
    (crtCharacter α β).conductor = α.conductor * β.conductor ∧
    ((crtCharacter α β) ^ 2).conductor = β.conductor ∧
    ((crtCharacter α β) ^ 3).conductor = α.conductor ∧
    ((crtCharacter α β) ^ 4).conductor = β.conductor ∧
    ((crtCharacter α β) ^ 5).conductor = α.conductor * β.conductor := by
  let a := DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α
  let b := DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β
  have hb3 : b ^ 3 = 1 := by
    have hh := orderOf_injective (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m))
      (DirichletCharacter.changeLevel_injective _) β
    rw [hβ] at hh
    exact orderOf_dvd_iff_pow_eq_one.mp (hh.symm ▸ dvd_refl 3)
  have hb2 : b ^ 2 = b⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ,hb3]
  have hcop : Nat.Coprime a.conductor b.conductor := by
    dsimp only [a,b]
    rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel]
    exact Nat.Coprime.of_dvd_right β.conductor_dvd_level
      (Nat.Coprime.of_dvd_left α.conductor_dvd_level hmn)
  have hp2 := crtCharacter_powers α β hα hβ 2
  have hp3 := crtCharacter_powers α β hα hβ 3
  have hp4 := crtCharacter_powers α β hα hβ 4
  have hp5 := crtCharacter_powers α β hα hβ 5
  norm_num only [pow_zero,pow_one,one_mul,mul_one] at hp2 hp3 hp4 hp5
  change (crtCharacter α β) ^ 2 = b ^ 2 at hp2
  change (crtCharacter α β) ^ 3 = a at hp3
  change (crtCharacter α β) ^ 4 = b at hp4
  change (crtCharacter α β) ^ 5 = a * b ^ 2 at hp5
  have haC : a.conductor = α.conductor := DirichletCharacter.conductor_changeLevel α _
  have hbC : b.conductor = β.conductor := DirichletCharacter.conductor_changeLevel β _
  have hc : (crtCharacter α β).conductor = α.conductor * β.conductor := by
    exact (conductor_mul_of_coprime a b hcop).trans (congrArg₂ (· * ·) haC hbC)
  refine ⟨hc,?_,?_,?_,?_⟩
  · rw [hp2,hb2,DirichletCharacter.conductor_inv,hbC]
  · rw [hp3,haC]
  · rw [hp4,hbC]
  · rw [hp5,hb2,conductor_mul_of_coprime,DirichletCharacter.conductor_inv,haC,hbC]
    simpa only [DirichletCharacter.conductor_inv] using hcop

/-- At an integer coprime to the product level, the CRT character equals the
product of the original character values. Evaluate both pullbacks on that unit.
This identifies the explicit CRT construction with its arithmetic prime values. -/
theorem crtCharacter_apply_nat {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n) {a : ℕ}
    (ha : Nat.Coprime a (m * n)) : crtCharacter α β a = α a * β a := by
  have hl := DirichletCharacter.changeLevel_eq_cast_of_dvd' α (Nat.dvd_mul_right m n) ha.isCoprime
  have hr := DirichletCharacter.changeLevel_eq_cast_of_dvd' β (Nat.dvd_mul_left n m) ha.isCoprime
  simp only [Int.cast_natCast] at hl hr
  rw [crtCharacter,MulChar.mul_apply,hl,hr]
/-- The subgroup of product-level units on which the CRT product character is one.
It is the kernel of the induced unit homomorphism. The order-six theorem below
identifies its index and its annihilator for conductor-sensitive prime bounds. -/
noncomputable abbrev crtKernel {m n : ℕ} (α : DirichletCharacter ℂ m)
    (β : DirichletCharacter ℂ n) : Subgroup (ZMod (m * n))ˣ :=
  (crtCharacter α β).toUnitHom.ker
/-- For exact character orders two and three, the CRT unit kernel has index six.
Combine the general character-kernel index theorem with the product order.
This supplies the actual subgroup used by the analytic Theorem 1.3 branch. -/
theorem crtKernel_index {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) : (crtKernel α β).index = 6 := by
  exact (index_kernel_eq_order _).trans (crtCharacter_order α β hα hβ)
/-- For exact character orders two and three, the CRT kernel is the intersection
of the two lifted kernels. The third and fourth powers of the product recover
the two factors, so a unit lies in the product kernel exactly when both factors are one. -/
theorem crtKernel_eq_inf {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) :
    crtKernel α β = (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom.ker ⊓
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).toUnitHom.ker := by
  have h3 := crtCharacter_powers α β hα hβ 3
  have h4 := crtCharacter_powers α β hα hβ 4
  norm_num only [pow_zero,pow_one,one_mul,mul_one] at h3 h4
  ext u
  change (crtCharacter α β).toUnitHom u = 1 ↔
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) α).toUnitHom u = 1 ∧
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) β).toUnitHom u = 1
  constructor
  · intro hu
    have hv := congrArg Units.val hu
    simp only [MulChar.coe_toUnitHom,Units.val_one] at hv
    constructor
    · apply Units.ext
      simp only [MulChar.coe_toUnitHom,Units.val_one]
      rw [← h3,MulChar.pow_apply_coe,hv,one_pow]
    · apply Units.ext
      simp only [MulChar.coe_toUnitHom,Units.val_one]
      rw [← h4,MulChar.pow_apply_coe,hv,one_pow]
  · rintro ⟨hl,hr⟩
    apply Units.ext
    have hleft := congrArg Units.val hl
    have hright := congrArg Units.val hr
    simp only [MulChar.coe_toUnitHom,Units.val_one] at hleft hright ⊢
    rw [crtCharacter,MulChar.mul_apply,hleft,hright,one_mul]
/-- The quotient of product-level units by the CRT kernel is cyclic.
The first isomorphism theorem identifies it with a finite subgroup of complex units,
which is cyclic by the finite-subgroup theorem for integral domains. -/
theorem crtKernel_quotient_cyclic {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n) :
    IsCyclic ((ZMod (m * n))ˣ ⧸ crtKernel α β) := by
  let e := QuotientGroup.quotientKerEquivRange (crtCharacter α β).toUnitHom
  let : IsCyclic (crtCharacter α β).toUnitHom.range := isCyclic_of_injective_ringHom
    ((Units.coeHom ℂ).comp (crtCharacter α β).toUnitHom.range.subtype)
    (Units.val_injective.comp Subtype.val_injective)
  exact isCyclic_of_injective e.toMonoidHom e.injective
/-- For exact orders two and three, the CRT unit quotient has six elements.
Translate the index-six theorem into the cardinality of the quotient.
Together with cyclicity and the intersection description this realizes the C6 quotient. -/
theorem crtKernel_quotient_card {m n : ℕ} [NeZero m] [NeZero n]
    (α : DirichletCharacter ℂ m) (β : DirichletCharacter ℂ n)
    (hα : orderOf α = 2) (hβ : orderOf β = 3) :
    Nat.card ((ZMod (m * n))ˣ ⧸ crtKernel α β) = 6 := by
  rw [← Subgroup.index_eq_card,crtKernel_index α β hα hβ]

end PseudoPrime.NumberTheory
