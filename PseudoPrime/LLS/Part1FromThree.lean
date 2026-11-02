/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCatalog
public import PseudoPrime.LLS.Part1CoverageTransfer
public import PseudoPrime.LLS.Part1ThreeFourBounds

/-! # Original LLS Part 1 extended from q >= 3000 to q >= 3 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: 5 <= q < 3000 and a proper unit subgroup.
Claim: an outside prime lies within the original LLS Part 1 radius, without GRH.
Proof: apply finite product generation and the certified integer-cap comparisons.
Role: discharge the remaining finite range for the entrance from three. -/
theorem exists_prime_outside_lls_part1_finite {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 :=
  exists_prime_outside_part1_of_blocks part1ProductCodeBlock part1DivisorCodeBlock
    part1ProductCatalog_checks hq hQ H hH

/-- Input: GRH, q >= 3 and a proper unit subgroup.
Claim: the original LLS Part 1 conclusion with its unchanged correction formula.
Proof: combine the full finite range with the established analytic theorem above 3000.
Role: expose the improved entrance as a separate theorem from the paper statement. -/
theorem llsTheorem11S1_from_three_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        ∃ u : (ZMod q)ˣ,
          u ∉ H ∧
            (u : ZMod q) = (p : ZMod q) ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  obtain ⟨p, hp, hb⟩ :=
    lls_part1_from_three_of_finite_range hGRH
      (fun q _ hq hQ H hH ↦ exists_prime_outside_lls_part1_finite hq hQ H hH) q hq H hH
  obtain ⟨hp, hd, u, hu, heq⟩ := hp
  exact ⟨p, hp, hd, u, hu, heq, hb⟩

end PseudoPrime.LLS
