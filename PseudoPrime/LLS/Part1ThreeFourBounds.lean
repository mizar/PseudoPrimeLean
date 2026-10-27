/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1SmallRadiusBounds
public import PseudoPrime.LLS.SmallModulusGenerationBounds
public import PseudoPrime.LLS.Theorem11S1GRH

/-! # Unconditional finite LLS Part 1 bounds at moduli three and four -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a prime label p and a residue r. Definition: the root one has depth zero;
other residues have parent one, label p and depth one.
Output: generation-tree data. Role: provide compact certificates for moduli three and four. -/
def twoElementPrimeGenerationTree (p r : ℕ) : NumberTheory.UnitGenerationNode :=
  ⟨1, p, if r = 1 then 0 else 1⟩

/-- Claim: the two residues modulo three form a valid generation tree with prime cap two.
Proof: kernel-check the complete finite invariant. Role: certify generation without GRH. -/
theorem twoElementPrimeGenerationTree_three_valid :
    NumberTheory.UnitGenerationTreeValid 3 2 (twoElementPrimeGenerationTree 2) := by decide +kernel

/-- Claim: the four residues modulo four form a valid generation tree with prime cap three.
Proof: kernel-check all units and nonunits. Role: certify generation without GRH. -/
theorem twoElementPrimeGenerationTree_four_valid :
    NumberTheory.UnitGenerationTreeValid 4 3 (twoElementPrimeGenerationTree 3) := by decide +kernel

/-- Input: a proper subgroup of the units modulo three.
Claim: an outside prime at most two lies within the original Part 1 radius.
Proof: use the finite tree and the proved radius lower bound. Role: the q=3 extension. -/
theorem exists_prime_outside_lls_part1_three (H : Subgroup (ZMod 3)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup 3 H p ∧ p ≤ 2 ∧ (p : ℝ) ≤ (Real.log 3 + llsCorrectionTerm 3) ^ 2 := by
  obtain ⟨p, hp, hb⟩ :=
    exists_prime_outside_of_generation_tree twoElementPrimeGenerationTree_three_valid H hH
  have hr :=
    lls_part1_radius_sq_ge_sixteen_three_four (by norm_num only : 3 ≤ 3) (by norm_num only : 3 ≤ 4)
  exact ⟨p, hp, hb, (Nat.cast_le.mpr hb).trans ((by norm_num only : (2 : ℝ) ≤ 16).trans hr)⟩

/-- Input: a proper subgroup of the units modulo four.
Claim: an outside prime at most three lies within the original Part 1 radius.
Proof: use the finite tree and the proved radius lower bound. Role: the q=4 extension. -/
theorem exists_prime_outside_lls_part1_four (H : Subgroup (ZMod 4)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup 4 H p ∧ p ≤ 3 ∧ (p : ℝ) ≤ (Real.log 4 + llsCorrectionTerm 4) ^ 2 := by
  obtain ⟨p, hp, hb⟩ :=
    exists_prime_outside_of_generation_tree twoElementPrimeGenerationTree_four_valid H hH
  have hr :=
    lls_part1_radius_sq_ge_sixteen_three_four (by norm_num only : 3 ≤ 4) (by norm_num only : 4 ≤ 4)
  exact ⟨p, hp, hb, (Nat.cast_le.mpr hb).trans ((by norm_num only : (3 : ℝ) ≤ 16).trans hr)⟩

/-- Input: any proper subgroup of the units modulo three. Claim: prime two is outside it.
Proof: every prime at most two is two. Role: identify the explicit finite witness. -/
theorem prime_two_outside_subgroup_three (H : Subgroup (ZMod 3)ˣ) (hH : H ≠ ⊤) :
    PrimeOutsideSubgroup 3 H 2 := by
  obtain ⟨p, hp, hb⟩ :=
    exists_prime_outside_of_generation_tree twoElementPrimeGenerationTree_three_valid H hH
  have heq : p = 2 := Nat.le_antisymm hb hp.1.two_le
  exact heq ▸ hp

/-- Input: any proper subgroup of the units modulo four. Claim: prime three is outside it.
Proof: a prime at most three not dividing four must equal three.
Role: identify the explicit finite witness. -/
theorem prime_three_outside_subgroup_four (H : Subgroup (ZMod 4)ˣ) (hH : H ≠ ⊤) :
    PrimeOutsideSubgroup 4 H 3 := by
  obtain ⟨p, hp, hb⟩ :=
    exists_prime_outside_of_generation_tree twoElementPrimeGenerationTree_four_valid H hH
  have hne : p ≠ 2 := fun heq ↦ hp.2.1 (heq.symm ▸ (by decide +kernel : 2 ∣ 4))
  have hlow : 3 ≤ p := Nat.lt_of_le_of_ne hp.1.two_le hne.symm
  exact (Nat.le_antisymm hb hlow) ▸ hp

/-- Input: 3 <= q <= 4 and a proper unit subgroup.
Claim: the original LLS Part 1 conclusion holds without GRH.
Proof: split the two possible moduli and apply the finite results.
Role: discharge both smallest moduli in a future extension from q >= 3. -/
theorem exists_prime_outside_lls_part1_three_four {q : ℕ} [NeZero q] (hq : 3 ≤ q) (hQ : q ≤ 4)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  rcases Nat.eq_or_lt_of_le hq with heq | hlt
  · subst q
    obtain ⟨p, hp, _, hb⟩ := exists_prime_outside_lls_part1_three H hH
    exact ⟨p, hp, hb⟩
  · have heq : q = 4 := Nat.le_antisymm hQ hlt
    subst q
    obtain ⟨p, hp, _, hb⟩ := exists_prime_outside_lls_part1_four H hH
    exact ⟨p, hp, hb⟩

/-- Input: GRH and the original-radius conclusion for every 5 <= q < 3000.
Claim: the original-radius conclusion holds for every q >= 3.
Proof: combine the checked two small moduli, the supplied finite range and the analytic theorem.
Role: expose precisely the remaining finite premise for the lowered entrance. -/
theorem lls_part1_from_three_of_finite_range
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hfinite :
      ∀ (q : ℕ) [NeZero q],
        5 ≤ q →
          q < 3000 →
          ∀ H : Subgroup (ZMod q)ˣ,
            H ≠ ⊤ →
              ∃ p : ℕ,
                PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2) :
    ∀ (q : ℕ) [NeZero q],
      3 ≤ q →
        ∀ H : Subgroup (ZMod q)ˣ,
          H ≠ ⊤ →
            ∃ p : ℕ,
              PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  intro q _ hq H hH
  by_cases hlarge : 3000 ≤ q
  · obtain ⟨p, hp, hd, u, hu, heq, hb⟩ := llsTheorem11S1_of_grh hGRH q hlarge H hH
    exact ⟨p, ⟨hp, hd, u, hu, heq⟩, hb⟩
  · by_cases hsmall : q ≤ 4
    · exact exists_prime_outside_lls_part1_three_four hq hsmall H hH
    · exact hfinite q (Nat.lt_of_not_ge hsmall) (Nat.lt_of_not_ge hlarge) H hH

end PseudoPrime.LLS
