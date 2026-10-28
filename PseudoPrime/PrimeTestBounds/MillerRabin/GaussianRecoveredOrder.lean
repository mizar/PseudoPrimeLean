/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianRecoveredOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextIntervalSelection

/-! # Strict Gaussian improvement over the current selected envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For natural inputs above one with logarithm in [132,215], the single-root
Gaussian cutoff strictly improves the current selected envelope. Use its exact
two-candidate middle-interval formula and both continuous comparisons. -/
theorem gaussianSingle_lt_next {n : ℕ} (hn : 1 < n) (hL : 132 ≤ Real.log n)
    (hU : Real.log n ≤ 215) :
    Analysis.gaussianSingleBound (Real.log n) < nextSelectedEnvelope n := by
  rw [← next_eq_selected hn, next_eq_middle_two hn hL (by linarith only [hU])]
  exact lt_min (Analysis.gaussianSingle_lt_pointwise hL) (Analysis.gaussianSingle_lt_original hL hU)

/-- For natural inputs above one with logarithm in [132,235], the recovered
Gaussian cutoff strictly improves the current selected envelope. The decreased
large-index root supplies strictness even beyond the old root crossing. -/
theorem gaussianRecovered_lt_next {n : ℕ} (hn : 1 < n) (hL : 132 ≤ Real.log n)
    (hU : Real.log n ≤ 235) :
    Analysis.gaussianRecoveredBound (Real.log n) < nextSelectedEnvelope n := by
  rw [← next_eq_selected hn, next_eq_middle_two hn hL hU]
  exact
    lt_min (Analysis.gaussianRecovered_lt_pointwise hL) (Analysis.gaussianRecovered_lt_original hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
