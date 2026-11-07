/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFirstGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030NonuniformLog8

/-! # First two adjacent Gamma cells for arbitrary odd composites -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite in the first two adjacent Gamma cells has
a prime Miller–Rabin rejecting base below the coefficient 0.3 cutoff.
Split the uniform Korselt triple at the common endpoint and use the existing
nonuniform theorem for all other factor types. -/
theorem exists_reject_03_first_two_cells {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (9977 / 250 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (gammaSecondRight : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · by_cases h : Real.log n ≤ (gammaFirstRight : ℝ)
    · exact uniform_first_cell_reject hn ho hu hGRH hlo h
    · apply uniform_second_cell_reject hn ho hu hGRH _ hhi
      simpa only [gammaFirstRight, Rat.cast_div, Rat.cast_ofNat] using (le_of_not_ge h)
  · apply exists_prime_reject_03_nonuniform_log8 hn ho hc hu hGRH
    linarith only [hlo]

end PseudoPrime.PrimeTestBounds.MillerRabin
