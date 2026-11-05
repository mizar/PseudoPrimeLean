/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PreciseLogTaylorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.IndexedPrimeSupplies

/-! # Prime supply and logarithms for the first repeated-product candidate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At least five primes are at most eleven. The zero-indexed fourth prime is
eleven; the existing prime-index count transfers this supply to any degree. -/
theorem prime_count_eleven_ge_five : 5 ≤ (11 : ℕ).primeCounting := by
  exact indexedSupplies_sound (11, 5) (by decide +kernel)

set_option maxRecDepth 8192 in
/-- The rational endpoints for the `B = 11`, `M = 5`, `k = 2` candidate
bound `2 log 11` from above and `log choose(7,2)` strictly from below.
Refined Taylor interval checks certify both logarithms by kernel reduction.
These endpoints support the first square and semiprime coverage candidate. -/
theorem count_eleven_degree_two_logs :
    (2 : ℝ) * Real.log 11 ≤ (2397895272799 / 500000000000 : ℝ) ∧
      (3044522437723 / 1000000000000 : ℝ) < Real.log (Nat.choose (5 + 2) 2 : ℝ) := by
  have hb : Analysis.preciseLogCheck 11 4 64 2 (2397895272799 / 1000000000000) = true := by
    decide +kernel
  have hc : Analysis.preciseLogCheck 21 5 64 (30445224377231 / 10000000000000) 4 = true := by
    decide +kernel
  have hb' := (Analysis.preciseLogCheck_sound hb).2
  have hc' := (Analysis.preciseLogCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.reduceAdd, Nat.choose] at hb' hc' ⊢
  constructor
  · linarith only [hb']
  · linarith only [hc']

end PseudoPrime.PrimeTestBounds.MillerRabin
