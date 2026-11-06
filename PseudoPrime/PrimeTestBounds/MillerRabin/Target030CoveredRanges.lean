/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Low394
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformGaussian

/-! # Covered 0.30 ranges for all odd composites -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm in `[8, 39.4]` or at
least 5250 has a prime rejecting it within coefficient 0.30. The low and
Gaussian high range bounds supply the two cases. -/
theorem exists_prime_reject_03_covered_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover : Real.log n ≤ 197 / 5 ∨ 5250 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  rcases hcover with hlow | hhigh
  · exact exists_prime_reject_03_log8_to_394 hn ho hc hGRH hL hlow
  · exact exists_prime_reject_03_log5250 hn ho hc hGRH hhigh

end PseudoPrime.PrimeTestBounds.MillerRabin
