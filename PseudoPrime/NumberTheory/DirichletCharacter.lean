/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Tactic

/-!
# Conductors and primitive normalization of Dirichlet characters

Evaluate characters that factor through a smaller level, transport integer-valued
factorizations to complex values, and preserve quadraticity under primitive normalization.
The coprime conductor product formula certifies primitivity of cross-level products.
-/

@[expose] public section

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

/-- For a quadratic character over a nontrivial commutative ring without zero divisors,
its primitive normalization is quadratic. Change of level preserves squares and recovers
the original character; injectivity transfers the square-one identity to the primitive
character. This supplies quadraticity after primitive normalization. -/
theorem isQuadratic_primitiveCharacter {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic) :
    χ.primitiveCharacter.IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, map_one]
  exact hχ.sq_eq_one

/-- For two complex characters at the same level with coprime conductors, the conductor
of their product is exactly the product of the conductors. Apply the conductor divisibility
bound to the product and each inverse character, then cancel the coprime conductor factors.
This identifies exact conductors of quadratic character products. -/
theorem conductor_mul_of_coprime {n : ℕ} (χ ψ : DirichletCharacter ℂ n)
    (hc : Nat.Coprime χ.conductor ψ.conductor) : (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  have hχ := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
  simp only [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at hχ
  have hψ := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ⁻¹ (χ * ψ)
  simp only [inv_mul_cancel_left, DirichletCharacter.conductor_inv] at hψ
  have h1 := hc.dvd_mul_right.mp (dvd_trans hχ (Nat.lcm_dvd_mul _ _))
  have h2 := hc.symm.dvd_mul_left.mp (dvd_trans hψ (Nat.lcm_dvd_mul _ _))
  apply Nat.dvd_antisymm
  · rw [← hc.lcm_eq_mul]
    exact DirichletCharacter.conductor_mul_dvd_lcm_conductor χ ψ
  · exact hc.mul_dvd_of_dvd_of_dvd h1 h2

/-- The cross-level product of primitive complex characters at coprime nonzero levels
is primitive at their least common multiple, which equals the product of the levels.
Changing levels preserves conductors, and the coprime product formula identifies
the conductor with the new level.
This combines odd and two-primary parts of a quadratic character. -/
theorem primitive_mul_of_coprime {n m : ℕ} [NeZero n] [NeZero m] (χ : DirichletCharacter ℂ n)
    (ψ : DirichletCharacter ℂ m) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hc : Nat.Coprime n m) :
    (DirichletCharacter.mul χ ψ).IsPrimitive := by
  let : NeZero (n.lcm m) := ⟨Nat.lcm_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  change (DirichletCharacter.mul χ ψ).conductor = n.lcm m
  rw [DirichletCharacter.mul, conductor_mul_of_coprime, DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_changeLevel, hχ, hψ, hc.lcm_eq_mul]
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel, hχ, hψ]
  exact hc

end PseudoPrime.NumberTheory
