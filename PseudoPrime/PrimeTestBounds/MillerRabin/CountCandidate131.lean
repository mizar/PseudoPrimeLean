/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.HighPrecisionLogBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.IndexedPrimeSupplies

/-! # A tight repeated-product candidate at 131 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At least 32 primes are at most 131. The prime index certificate gives the required supply
for repeated-product counting at this bound. -/
theorem prime_count_131_ge_32 : 32 ≤ (131 : ℕ).primeCounting := by
  exact indexedSupplies_sound (131, 32) (by decide +kernel)

set_option maxRecDepth 16384 in
/-- For the candidate with bound 131, supply 32 and degree 3, the rational endpoints bound
`3 log 131` above and `log (choose 35 3)` strictly below. The second endpoint is extremely
close to the logarithm, so a higher-precision Taylor certificate is used for that side. -/
theorem count_131_degree_three_logs :
    (3 : ℝ) * Real.log 131 ≤ (7312795984803 / 500000000000 : ℝ) ∧
      (1098307084793 / 125000000000 : ℝ) < Real.log (Nat.choose (32 + 3) 3 : ℝ) := by
  have hb : Analysis.preciseLogCheck 131 8 64 4 (2437598661601 / 500000000000) = true := by
    decide +kernel
  have hc :
    Analysis.fineLogCheck 6545 13 128 (1098307084793 / 125000000000 + 1 / 1000000000000000000)
        (8786456678347 / 1000000000000) =
      true := by
    decide +kernel
  have hb' := (Analysis.preciseLogCheck_sound hb).2
  have hc' := (Analysis.fineLogCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_add, Nat.reduceAdd, Nat.choose] at hb' hc' ⊢
  constructor
  · linarith only [hb']
  · linarith only [hc']

end PseudoPrime.PrimeTestBounds.MillerRabin
