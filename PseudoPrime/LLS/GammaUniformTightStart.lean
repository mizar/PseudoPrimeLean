/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformReducedStart
public import PseudoPrime.LLS.GammaUniformLocalBudgetParameters
public import PseudoPrime.LLS.PaperStatements.GammaUniformTightStart

/-! # Tighter uniform coefficient-four-fifths starting value

Refined rational square-root and logarithmic-ratio certificates lower the common
logarithmic start to 45561. The decimal logarithm gives 10^19787 for subgroup,
general-character and least-prime witnesses, with the same analytic kernel.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 10 ^ 19787 and χ nonprincipal, there is a prime p coprime
to q with χ(p) ≠ 1 and p ≤ (4 / 5)(log q) ^ 2. Apply the uniform proper-subgroup
bound to the unit kernel and translate nonmembership into a non-one value.
This improves the large-level general-character form of LLS Theorem 1.1. -/
theorem exists_prime_character_ne_one_le_gamma_four_fifths_19787 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    PaperStatements.exists_prime_outside_le_gamma_four_fifths_19787 χ.toUnitHom.ker
      (NumberTheory.ker_toUnitHom_ne_top_of_ne_one χ hne) hGRH hq
  refine ⟨p, hp, hd, ?_, hb⟩
  intro he
  have hc := hp.coprime_iff_not_dvd.mpr hd
  have hu := (ZMod.isUnit_iff_coprime p q).mpr hc
  apply hout
  refine ⟨hu.unit, ?_, IsUnit.unit_spec hu⟩
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  simpa only [MulChar.coe_toUnitHom, Units.val_one, IsUnit.unit_spec] using he

/-- Under GRH, q ≥ 10 ^ 19787 and H proper, the project predicate for a prime
outside H has a witness at most (4 / 5)(log q) ^ 2. Recover the residue unit from
coprimality and transfer the uniform subgroup witness to the existing predicate.
This is the existence interface used to construct the least outside prime. -/
theorem exists_prime_outside_subgroup_le_gamma_four_fifths_19787 {q : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 := by
  obtain ⟨p, hp, hd, hout, hb⟩ :=
    PaperStatements.exists_prime_outside_le_gamma_four_fifths_19787 H hH hGRH hq
  have hu := (ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd)
  refine ⟨p, ⟨hp, hd, hu.unit, ?_, IsUnit.unit_spec hu⟩, hb⟩
  intro hm
  exact hout ⟨hu.unit, hm, IsUnit.unit_spec hu⟩

/-- Under GRH, q ≥ 10 ^ 19787 and H proper, the least prime coprime to q
outside H is at most (4 / 5)(log q) ^ 2. Minimize the unbounded prime predicate
using the bounded existence witness. Minimality holds among all eligible primes,
without restricting the comparison candidates to the displayed upper bound. -/
theorem exists_least_prime_outside_subgroup_le_gamma_four_fifths_19787 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 19787 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log q) ^ 2 ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_gamma_four_fifths_19787 H hH hGRH hq
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hp)).trans hb, fun _ hr ↦
      Nat.find_min' hex hr⟩

end PseudoPrime.LLS
