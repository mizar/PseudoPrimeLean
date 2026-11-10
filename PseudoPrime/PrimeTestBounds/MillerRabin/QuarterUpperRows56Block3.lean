/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block3 : List QuarterUpperWeightRow :=
  [⟨56, 79, 0, 343, 346, 2461, 2465, 8888, 11716522197, 7283⟩,
    ⟨56, 81, 1, 368, 371, 2434, 2438, 9000, 11404408588, 6994⟩,
    ⟨56, 83, 1, 392, 395, 2408, 2412, 9110, 11111715464, 6721⟩,
    ⟨56, 89, 1, 462, 465, 2332, 2337, 9433, 10298517973, 5980⟩,
    ⟨56, 97, 1, 548, 551, 2239, 2244, 9848, 9383942643, 5131⟩,
    ⟨56, 101, 1, 588, 591, 2196, 2200, 10049, 8988985537, 4755⟩,
    ⟨56, 103, 1, 608, 611, 2175, 2179, 10148, 8802185112, 4583⟩,
    ⟨56, 107, 1, 646, 649, 2134, 2138, 10344, 8448593677, 4260⟩,
    ⟨56, 109, 1, 664, 667, 2114, 2118, 10440, 8281300315, 4109⟩,
    ⟨56, 113, 1, 701, 704, 2074, 2078, 10630, 7956585884, 3818⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block3_check :
    quarterUpperRows56Block3.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
