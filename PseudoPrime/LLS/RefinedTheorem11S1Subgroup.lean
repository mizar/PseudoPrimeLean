/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S1
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Proper-subgroup prime bounds for the refined Part 1 radius -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, q≥3000 and a proper subgroup H give a prime outside H below
the refined Part 1 radius squared. Pull back a nonprincipal character of the quotient,
apply the refined character witness theorem, and use triviality of the pullback on H.
This gives the subgroup form of the improved correction with additive constant two. -/
theorem exists_prime_outside_subgroup_le_refinedRadius {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (refinedRadiusRoot q) ^ 2 := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx1⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχx⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx1
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    exists_prime_character_ne_one_le_refinedRadius (pullbackCharacter χ') hq
      (pullbackCharacter_ne_one_of_ne_one χ' hχx) hGRH
  have hc : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hd
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hc
  refine ⟨p, ⟨hp, hd, hu.unit, ?_, IsUnit.unit_spec hu⟩, hb⟩
  intro hm
  apply hv
  have he := pullbackCharacter_eq_one_of_mem χ' (H := H) hm
  rwa [IsUnit.unit_spec hu] at he

/-- Under GRH and q≥3000, the least prime outside a proper subgroup is bounded
by the refined Part 1 radius squared. Minimize the unbounded prime predicate
using the bounded existence witness. This adds minimality without checking any prime table. -/
theorem exists_least_prime_outside_subgroup_le_refinedRadius {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (refinedRadiusRoot q) ^ 2 ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_refinedRadius hq H hH hGRH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hp)).trans hb, fun _ hr ↦
      Nat.find_min' hex hr⟩

end PseudoPrime.LLS
