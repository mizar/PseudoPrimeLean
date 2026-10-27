/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogRootSmallLevelBounds
public import PseudoPrime.LLS.Part2FromFive
public import PseudoPrime.LLS.ReciprocalCostPart2Bounds

/-! # LLS Part 2 with correction 2279/500 on every modulus from five -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: GRH, q>=5 and a proper subgroup of the unit group.
Claim: a prime outside its image lies at most (log q-2 log log q+2279/500)^2.
Proof: use the analytic reciprocal-cost theorem above 1120 and the finite log-square
witnesses below it, comparing their radii without combining formulas by a minimum.
Role: expose the stronger correction 4.558 with the full entrance q>=5. -/
theorem exists_prime_outside_reciprocalPart2_from_five
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.reciprocalPart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  by_cases hlarge : 1120 ≤ q
  · exact exists_prime_outside_subgroup_image_le_reciprocalPart2Root hlarge H hH hGRH
  · obtain ⟨p, hp, hb, hout⟩ :=
      exists_prime_outside_part2_finite hq
        (lt_of_lt_of_le (Nat.lt_of_not_ge hlarge) (by norm_num only : 1120 ≤ 3000)) H hH
    have hqR : (5 : ℝ) ≤ q := Nat.cast_le.mpr hq
    have hL : 0 < Real.log q := Real.log_pos (by linarith only [hqR])
    have hcap :=
      Analysis.logRoot_sq_ge_log_sq_of_small_level hL
        (Analysis.log_level_le_eight_of_lt1120 (NeZero.pos q) (Nat.lt_of_not_ge hlarge))
        (by norm_num only : (21 / 5 : ℝ) ≤ 2279 / 500)
    exact ⟨p, hp, hb.trans hcap, hout⟩

end PseudoPrime.LLS
