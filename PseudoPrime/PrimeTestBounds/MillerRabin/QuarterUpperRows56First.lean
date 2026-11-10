/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Initial principal upper rows at cutoff 56 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for the first ten prime powers. -/
def quarterUpperRows56First : List QuarterUpperWeightRow :=
  [⟨56, 2, 5, 3331, 3334, 6432, 6436, 1414, 621415537060, 104730⟩,
    ⟨56, 3, 4, 2925, 2928, 5994, 5998, 1732, 401015467921, 93142⟩,
    ⟨56, 4, 4, 2638, 2641, 5684, 5688, 2000, 294123574342, 84345⟩,
    ⟨56, 5, 3, 2414, 2417, 5442, 5446, 2236, 230903528994, 77323⟩,
    ⟨56, 7, 3, 2078, 2081, 5079, 5083, 2645, 160613362208, 66560⟩,
    ⟨56, 8, 3, 1944, 1947, 4934, 4938, 2828, 138934138877, 62271⟩,
    ⟨56, 9, 3, 1827, 1830, 4808, 4812, 3000, 122486399564, 58512⟩,
    ⟨56, 11, 2, 1626, 1629, 4591, 4595, 3316, 98592973835, 52214⟩,
    ⟨56, 13, 2, 1459, 1462, 4410, 4414, 3605, 82269463486, 47081⟩,
    ⟨56, 16, 2, 1251, 1254, 4186, 4190, 4000, 65759227257, 40915⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_first_check :
    quarterUpperRows56First.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
