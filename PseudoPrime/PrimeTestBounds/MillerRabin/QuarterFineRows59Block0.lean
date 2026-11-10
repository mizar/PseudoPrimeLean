/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 59, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows59Block0 : List QuarterFineWeightRow :=
  [⟨59, 2, 5, 33842, 33845, 64903, 14143, 1518093, 102985⟩,
    ⟨59, 3, 4, 29788, 29791, 60525, 17321, 2351974, 91877⟩,
    ⟨59, 4, 4, 26911, 26914, 57418, 20000, 3208986, 83414⟩,
    ⟨59, 5, 4, 24679, 24682, 55007, 22361, 4083911, 76621⟩,
    ⟨59, 7, 3, 21315, 21318, 51374, 26458, 5872939, 66171⟩,
    ⟨59, 8, 3, 19979, 19982, 49931, 28285, 6784599, 62012⟩,
    ⟨59, 9, 3, 18802, 18805, 48660, 30000, 7704120, 58359⟩,
    ⟨59, 11, 2, 16795, 16798, 46492, 33167, 9569254, 52206⟩,
    ⟨59, 13, 2, 15124, 15127, 44688, 36056, 11461060, 47186⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows59_block0_check :
    quarterFineRows59Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
