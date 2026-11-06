/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Low144
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformGaussian

/-! # Established 0.30 ranges through scale 14.4 and above 5250 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm at least 8 has a 0.30
rejecting prime on the established low and high ranges. The disjunction keeps
the intermediate range explicit. -/
theorem exists_prime_reject_03_ranges144 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover : Real.log n ≤ 72 / 5 ∨ 5250 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  rcases hcover with hlow | hhigh
  · exact exists_prime_reject_03_log8_to_144 hn ho hc hGRH hL hlow
  · exact exists_prime_reject_03_log5250 hn ho hc hGRH hhigh

end PseudoPrime.PrimeTestBounds.MillerRabin
