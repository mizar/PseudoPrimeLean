/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterIntersection50

/-! # Coefficient 0.28 through logarithmic scale 11.33 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm between 8 and 11.33 has a
rejecting prime below the 0.28 cutoff. The quarter-square bound is stronger. -/
theorem exists_prime_reject_028_through1133 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1133 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := quarter_all_8_50 hn ho hc hGRH hL (by linarith only [hU])
  have hcoef : (1 / 4 : ℝ) ≤ 7 / 25 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
