/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.MulChar.Duality
import PseudoPrime.LLS.Statement

/-!
# From the character-kernel bound to the proper-subgroup bound

This file converts `llsTheorem11S1Character`, stated for arbitrary nontrivial complex Dirichlet
characters, into `llsTheorem11S1`, stated for arbitrary proper subgroups `H` of `(ZMod q)ˣ`.

Given a proper subgroup `H`, the quotient `(ZMod q)ˣ ⧸ H` is a nontrivial finite commutative
group, so it carries a nontrivial `ℂ`-valued character
(`MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`). Pulling that character back along the
quotient map gives a Dirichlet character of level `q` that is trivial on `H` and not the trivial
character. Applying `llsTheorem11S1Character` to this pullback produces a prime with character
value different from `1`; since the pullback is trivial on `H`, its residue lies outside `H`.
-/

namespace PseudoPrime.LLS

variable {q : ℕ} [NeZero q]

/--
The Dirichlet character of level `q` obtained by pulling a character of the quotient group
`(ZMod q)ˣ ⧸ H` back along the quotient map.

Role: the common construction behind `pullbackCharacter_eq_one_of_mem` and
`pullbackCharacter_ne_one_of_ne_one`, consumed by `llsTheorem11S1_of_character`.
-/
noncomputable def pullbackCharacter {H : Subgroup (ZMod q)ˣ} (χ' : MulChar ((ZMod q)ˣ ⧸ H) ℂ) :
    DirichletCharacter ℂ q :=
  have : H.Normal := H.normal_of_isMulCommutative
  MulChar.ofUnitHom
    (χ'.toUnitHom.comp
      ((toUnits : (ZMod q)ˣ ⧸ H ≃* ((ZMod q)ˣ ⧸ H)ˣ).toMonoidHom.comp (QuotientGroup.mk' H)))

omit [NeZero q] in
/-- The pullback character evaluates on a unit `u` as `χ'` evaluates on the image of `u`. -/
theorem pullbackCharacter_apply {H : Subgroup (ZMod q)ˣ} (χ' : MulChar ((ZMod q)ˣ ⧸ H) ℂ)
    (u : (ZMod q)ˣ) :
    have : H.Normal := H.normal_of_isMulCommutative
    pullbackCharacter χ' (u : ZMod q) = χ' (QuotientGroup.mk' H u) := by
  have : H.Normal := H.normal_of_isMulCommutative
  unfold pullbackCharacter
  rw [MulChar.ofUnitHom_coe]
  simp [val_toUnits_apply]

omit [NeZero q] in
/-- The pullback character in `pullbackCharacter` is trivial on `H`. -/
theorem pullbackCharacter_eq_one_of_mem {H : Subgroup (ZMod q)ˣ} (χ' : MulChar ((ZMod q)ˣ ⧸ H) ℂ)
    {h : (ZMod q)ˣ} (hh : h ∈ H) : pullbackCharacter χ' (h : ZMod q) = 1 := by
  have : H.Normal := H.normal_of_isMulCommutative
  rw [pullbackCharacter_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).mpr hh,
    map_one]

omit [NeZero q] in
/--
The pullback character in `pullbackCharacter` is not the trivial character, provided the
character `χ'` of the quotient is nontrivial at some point `x`.
-/
theorem pullbackCharacter_ne_one_of_ne_one {H : Subgroup (ZMod q)ˣ} (χ' : MulChar ((ZMod q)ˣ ⧸ H) ℂ)
    {x : (ZMod q)ˣ ⧸ H} (hx : χ' x ≠ 1) : pullbackCharacter χ' ≠ 1 := by
  have : H.Normal := H.normal_of_isMulCommutative
  intro hcontra
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective H x
  apply hx
  rw [← hu, ← pullbackCharacter_apply, hcontra]
  exact MulChar.one_apply_coe u

/--
The proper-subgroup conclusion of LLS Theorem 1.1 follows from the character-kernel
specialization `llsTheorem11S1Character` by pulling back a nontrivial character of `(ZMod q)ˣ ⧸ H`.
-/
theorem llsTheorem11S1_of_character (h11 : llsTheorem11S1Character) : llsTheorem11S1 := by
  intro q _ hq H hH
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx1⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ'x⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx1
  obtain ⟨ℓ, hℓprime, hℓndvd, hℓne1, hℓbound⟩ :=
    h11 q (pullbackCharacter χ') hq (pullbackCharacter_ne_one_of_ne_one χ' hχ'x)
  have hcop : Nat.Coprime ℓ q := hℓprime.coprime_iff_not_dvd.mpr hℓndvd
  have hunit : IsUnit ((ℓ : ZMod q)) := (ZMod.isUnit_iff_coprime ℓ q).mpr hcop
  refine ⟨ℓ, hℓprime, hℓndvd, hunit.unit, ?_, IsUnit.unit_spec hunit, hℓbound⟩
  intro hmem
  apply hℓne1
  have := pullbackCharacter_eq_one_of_mem χ' (H := H) hmem
  rwa [IsUnit.unit_spec hunit] at this

/-- A prime not dividing `q` whose unit residue lies outside `H`.
The witness unit records the residue equality explicitly. This predicate is used to
minimize the primes supplied by the proper-subgroup form of Theorem 1.1. -/
def PrimeOutsideSubgroup (q : ℕ) (H : Subgroup (ZMod q)ˣ) (p : ℕ) : Prop :=
  p.Prime ∧ ¬p ∣ q ∧ ∃ u : (ZMod q)ˣ, u ∉ H ∧ (u : ZMod q) = (p : ZMod q)

/-- The S1 existence bound also bounds the least prime outside a proper subgroup.
For `q ≥ 3000`, minimize the unbounded prime predicate with `Nat.find`; its least
element is no larger than the bounded witness. This supplies the minimality conclusion
without changing the existing existence specification. -/
theorem exists_least_prime_outside_subgroup_of_s1 (hS1 : llsTheorem11S1)
    (hq : 3000 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p, PrimeOutsideSubgroup q H p ∧
      (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 ∧
      ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hpq, u, hu, hup, hb⟩ := hS1 q hq H hH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp, hpq, u, hu, hup⟩
  exact ⟨Nat.find hex, Nat.find_spec hex,
    (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hpq, u, hu, hup⟩)).trans hb,
    fun _ hr ↦ Nat.find_min' hex hr⟩

end PseudoPrime.LLS
