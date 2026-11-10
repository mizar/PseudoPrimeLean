/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 14 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block14 : List QuarterUpperWeightRow :=
  [⟨56, 653, 4, 2455, 2458, 180, 184, 25553, 1197217362, 1⟩,
    ⟨56, 659, 4, 2464, 2467, 170, 174, 25670, 1185304849, 1⟩,
    ⟨56, 661, 4, 2467, 2470, 167, 171, 25709, 1181754263, 1⟩,
    ⟨56, 673, 4, 2485, 2488, 147, 152, 25942, 1158353962, 1⟩,
    ⟨56, 677, 4, 2491, 2494, 141, 145, 26019, 1151424645, 1⟩,
    ⟨56, 683, 4, 2500, 2503, 131, 135, 26134, 1139967779, 1⟩,
    ⟨56, 691, 4, 2511, 2514, 119, 124, 26286, 1126369915, 1⟩,
    ⟨56, 701, 4, 2526, 2529, 103, 107, 26476, 1108491407, 1⟩,
    ⟨56, 709, 4, 2537, 2540, 91, 96, 26627, 1095269003, 1⟩,
    ⟨56, 719, 4, 2551, 2554, 76, 80, 26814, 1078962573, 1⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block14_check :
    quarterUpperRows56Block14.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
