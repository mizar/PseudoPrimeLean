/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028High
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedTriangularWidth24

/-! # High-range witnesses with coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Assuming GRH, an odd composite with logarithm at least 2000 has a rejecting prime
at most `7 / 25` times the squared logarithm. Compare the existing piecewise witness
with the uniform high-range bound. -/
theorem exists_prime_reject_028_high {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (2000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := refined_piecewise_witness hn ho hc hGRH (by linarith only [hL])
  exact ⟨p, hp, hb.trans (target028_piecewise_le hL), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
