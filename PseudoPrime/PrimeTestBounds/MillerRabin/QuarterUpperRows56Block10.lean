/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block10 : List QuarterUpperWeightRow :=
  [⟨56, 421, 3, 2016, 2019, 654, 658, 20518, 1923218334, 27⟩,
    ⟨56, 431, 3, 2039, 2042, 629, 633, 20760, 1875733902, 22⟩,
    ⟨56, 433, 3, 2044, 2047, 624, 628, 20808, 1866378643, 21⟩,
    ⟨56, 439, 3, 2058, 2061, 609, 613, 20952, 1838591884, 19⟩,
    ⟨56, 443, 3, 2067, 2070, 599, 603, 21047, 1820297586, 18⟩,
    ⟨56, 449, 3, 2080, 2083, 585, 589, 21189, 1794990982, 16⟩,
    ⟨56, 457, 3, 2098, 2101, 565, 570, 21377, 1759447779, 14⟩,
    ⟨56, 461, 3, 2107, 2110, 556, 560, 21470, 1743683792, 13⟩,
    ⟨56, 463, 3, 2111, 2114, 551, 556, 21517, 1734987133, 12⟩,
    ⟨56, 467, 3, 2119, 2122, 543, 547, 21610, 1721162609, 11⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block10_check :
    quarterUpperRows56Block10.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
