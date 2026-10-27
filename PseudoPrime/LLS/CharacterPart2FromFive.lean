/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part2FromFive

/-! # Log-square non-one character witnesses from level five -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a nonprincipal complex Dirichlet character.
Claim: its restriction to the unit group has a proper kernel.
Proof: a full kernel would make the character one on every unit.
Role: transfer subgroup certificates to arbitrary nonprincipal characters. -/
theorem character_unit_kernel_ne_top {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    χ.toUnitHom.ker ≠ ⊤ := by
  intro h
  apply hne
  apply MulChar.eq_one_iff.mpr
  intro u
  have hu : u ∈ χ.toUnitHom.ker := h.symm ▸ Subgroup.mem_top u
  exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) (MonoidHom.mem_ker.mp hu)

/-- Input: a residue whose character value is one.
Claim: the residue is represented by a unit in the character kernel.
Proof: nonunits have value zero, and unit evaluation agrees with the unit homomorphism.
Role: turn exclusion from the kernel image into a character value different from one. -/
theorem exists_unit_kernel_representative_of_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : χ a = 1) : ∃ u : (ZMod q)ˣ, u ∈ χ.toUnitHom.ker ∧ (u : ZMod q) = a := by
  have hu : IsUnit a := by
    by_contra hn
    exact zero_ne_one ((χ.map_nonunit hn).symm.trans ha)
  refine ⟨hu.unit, MonoidHom.mem_ker.mpr ?_, hu.unit_spec⟩
  apply Units.ext
  exact (MulChar.coe_toUnitHom χ hu.unit).trans ((congrArg χ hu.unit_spec).trans ha)

/-- Input: a nonprincipal character at a level `5 ≤ q < 3000`.
Claim: a prime at most `(log q)^2` has character value different from one.
Proof: apply the finite subgroup certificate to the character kernel.
Role: provide the finite branch without GRH; zero character values are allowed. -/
theorem exists_prime_not_one_le_log_sq_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 5 ≤ q) (hQ : q < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Real.log q) ^ 2 ∧ χ p ≠ 1 := by
  obtain ⟨p, hp, hb, hout⟩ :=
    exists_prime_outside_part2_finite hq hQ χ.toUnitHom.ker (character_unit_kernel_ne_top χ hne)
  exact ⟨p, hp, hb, fun h ↦ hout (exists_unit_kernel_representative_of_eq_one χ h)⟩

/-- Input: GRH and a nonprincipal character at a level `q ≥ 5`.
Claim: a prime at most `(log q)^2` has character value different from one.
Proof: use the finite kernel certificate below 3000 and the analytic theorem above it.
Role: extend the character version of LLS Part 2 to the entrance from five. -/
theorem exists_prime_not_one_le_log_sq_from_five {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 5 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Real.log q) ^ 2 ∧ χ p ≠ 1 := by
  by_cases hlarge : 3000 ≤ q
  · exact exists_prime_not_one_le_log_sq χ hne hlarge hGRH
  · exact exists_prime_not_one_le_log_sq_finite χ hne hq (Nat.lt_of_not_ge hlarge)

/-- Input: GRH, a level `q ≥ 5`, and a proper subgroup of its unit group.
Claim: a prime at most `(log q)^2` lies outside the subgroup image.
Proof: pull back a nonprincipal quotient character and apply the entrance from five.
Role: expose the subgroup consequence without a small-prime-exclusion premise. -/
theorem exists_prime_outside_subgroup_image_le_log_sq_from_five {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hn⟩ :=
    exists_prime_not_one_le_log_sq_from_five (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, heq⟩
  apply hn
  rw [← heq]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
