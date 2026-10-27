/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part2SmallFinite
public import PseudoPrime.LLS.Theorem11S2

/-! # Original LLS Part 2 extended from q >= 3000 to q >= 5 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: 5 <= q < 3000 and a proper subgroup of the unit group.
Claim: a prime at most (log q)^2 lies outside its image, without GRH or prime exclusion.
Proof: combine the small exact checks with the reused full catalog above 79.
Role: discharge the entire finite premise for the entrance from five. -/
theorem exists_prime_outside_part2_finite {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  by_cases hsmall : q < 79
  · exact exists_prime_outside_part2_small_finite hq hsmall H hH
  · exact exists_prime_outside_part2_large_finite (Nat.le_of_not_gt hsmall) hQ H hH

/-- Input: GRH, q >= 5, the original strict small-prime-exclusion premise,
and a proper subgroup of the unit group.
Claim: the original Part 2 prime-outside-image conclusion with unchanged log-square cutoff.
Proof: use the GRH-free finite theorem below 3000 and the established analytic theorem above it.
Role: expose the improved entrance separately from the unchanged paper specification. -/
theorem llsTheorem11S2_from_five_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (q : ℕ) [NeZero q] (hq : 5 ≤ q)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) < (Real.log q) ^ 2 → ¬p ∣ q) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  by_cases hlarge : 3000 ≤ q
  · exact llsTheorem11S2_of_grh hGRH q hlarge hsmall H hH
  · exact exists_prime_outside_part2_finite hq (Nat.lt_of_not_ge hlarge) H hH

end PseudoPrime.LLS
