/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

namespace PseudoPrime.NumberTheory

/-- A factor-through character takes value `1` on a unit congruent to `1` modulo its
factor level. -/
theorem factorsThrough_apply_eq_one_of_one_modEq {R : Type*} [CommMonoidWithZero R] {d c a : ℕ}
    {χ : DirichletCharacter R d} (hχ : χ.FactorsThrough c) (ha : a ≡ 1 [MOD c])
    (hacop : Nat.Coprime a d) : χ (a : ℤ) = 1 := by
  rcases hχ with ⟨hc, χ₀, hχ⟩
  rw [hχ]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hc (Nat.isCoprime_iff_coprime.mpr hacop)]
  have hamod : (a : ℤ) % c = (1 : ℤ) % c := by exact_mod_cast ha
  have hcast : ((a : ℤ) : ZMod c) = 1 := by
    calc
      ((a : ℤ) : ZMod c) = ((1 : ℤ) : ZMod c) :=
        (ZMod.intCast_eq_intCast_iff' (a : ℤ) 1 c).mpr hamod
      _ = 1 := by norm_num only
  rw [hcast]
  exact χ₀.map_one

/-- A factor-through complex character cannot have value `-1` on a unit that is
congruent to `1` modulo the factor level. -/
theorem complexFactorsThrough_ne_neg_one_of_one_modEq {d c a : ℕ} {χ : DirichletCharacter ℂ d}
    (hχ : χ.FactorsThrough c) (ha : a ≡ 1 [MOD c]) (hacop : Nat.Coprime a d)
    (hvalue : χ (a : ℤ) = -1) : False := by
  have hone := factorsThrough_apply_eq_one_of_one_modEq hχ ha hacop
  rw [hvalue] at hone
  norm_num only at hone

/-- Ring-hom composition transports a factor-through witness from integer to complex values. -/
theorem factorsThrough_ringHomComp_of_int {n d : ℕ} {χ : DirichletCharacter ℤ n}
    (hχ : DirichletCharacter.FactorsThrough χ d) :
    DirichletCharacter.FactorsThrough (χ.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ n)
      d := by
  rcases hχ with ⟨hd, χ₀, hχ⟩
  refine ⟨hd, (χ₀.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d), ?_⟩
  rw [hχ]
  ext a
  simp only [MulChar.ringHomComp, DirichletCharacter.changeLevel_def, MulChar.toUnitHom_eq,
    MulChar.ofUnitHom_eq, eq_intCast, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    MulChar.equivToUnitHom_symm_coe, MonoidHom.coe_comp, Function.comp_apply,
    MulChar.coe_equivToUnitHom]

end PseudoPrime.NumberTheory
