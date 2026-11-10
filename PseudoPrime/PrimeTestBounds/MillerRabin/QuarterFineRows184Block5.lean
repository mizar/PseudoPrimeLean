/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block5 : List QuarterFineWeightRow :=
  [⟨184, 137, 0, 2948, 2951, 31538, 117047, 42689597, 9476⟩,
    ⟨184, 139, 0, 2803, 2806, 31381, 117899, 43365113, 9322⟩,
    ⟨184, 149, 0, 2108, 2111, 30630, 122066, 46747242, 8599⟩,
    ⟨184, 151, 0, 1975, 1978, 30487, 122883, 47420530, 8464⟩,
    ⟨184, 157, 0, 1585, 1588, 30066, 125300, 49459555, 8075⟩,
    ⟨184, 163, 0, 1210, 1213, 29661, 127672, 51503783, 7712⟩,
    ⟨184, 167, 0, 968, 971, 29399, 129229, 52871015, 7483⟩,
    ⟨184, 169, 0, 849, 852, 29271, 130000, 53552114, 7371⟩,
    ⟨184, 173, 0, 615, 618, 29018, 131530, 54924267, 7155⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block5_check :
    quarterFineRows184Block5.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
