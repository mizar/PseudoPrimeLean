/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Contracts for uniform rational subgroup profiles -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A uniform subgroup profile bound gives a coprime outside prime for every
proper unit subgroup at each input above that profile's own starting value, under GRH.
The bound uses the profile's rational cutoff. This is the proof contract for a prepared tuple. -/
def UniformSubgroupProfileBound (profile : Analysis.RationalLogarithmicProfile) : Prop :=
  ∀ (q : ℕ) (H : Subgroup (ZMod q)ˣ),
    H ≠ ⊤ →
      AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
      profile.startingValue ≤ q → ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ profile.cutoff q

end PseudoPrime.LLS
