/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleRoundCombined
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaTwoCells

/-! # Low bridge joined to the first Gamma cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm between eight and the end
of the second Gamma cell has a rejecting prime within the `3/10` cutoff.
The low rounding bridge meets the first two Gamma cells at `39.908`. -/
theorem exists_reject_03_low_two_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (gammaSecondRight : ℝ)) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  by_cases h : Real.log n ≤ (9977 / 250 : ℝ)
  · exact exists_prime_reject_03_log8_39908 hn ho hc hGRH hL h
  · exact exists_reject_03_first_two_cells hn ho hc hGRH (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
