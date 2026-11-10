/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 12 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block12 : List QuarterUpperWeightRow :=
  [⟨56, 541, 3, 2267, 2270, 383, 387, 23259, 1466678026, 3⟩,
    ⟨56, 547, 3, 2278, 2281, 371, 375, 23388, 1449183068, 2⟩,
    ⟨56, 557, 3, 2296, 2299, 352, 356, 23600, 1421908519, 2⟩,
    ⟨56, 563, 3, 2306, 2309, 341, 345, 23727, 1406353237, 2⟩,
    ⟨56, 569, 3, 2317, 2320, 329, 333, 23853, 1389577852, 2⟩,
    ⟨56, 571, 3, 2321, 2324, 325, 329, 23895, 1384030643, 1⟩,
    ⟨56, 577, 3, 2331, 2334, 314, 318, 24020, 1368889734, 1⟩,
    ⟨56, 587, 3, 2348, 2351, 295, 300, 24228, 1343126356, 1⟩,
    ⟨56, 593, 3, 2358, 2361, 285, 289, 24351, 1329762026, 1⟩,
    ⟨56, 599, 3, 2368, 2371, 274, 278, 24474, 1315214798, 1⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block12_check :
    quarterUpperRows56Block12.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
