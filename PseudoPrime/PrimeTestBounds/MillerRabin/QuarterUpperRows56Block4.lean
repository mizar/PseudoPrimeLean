/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block4 : List QuarterUpperWeightRow :=
  [⟨56, 121, 1, 769, 772, 2001, 2005, 11000, 7396448844, 3319⟩,
    ⟨56, 125, 1, 801, 804, 1966, 1970, 11180, 7142051062, 3097⟩,
    ⟨56, 127, 1, 817, 820, 1949, 1953, 11269, 7021662395, 2993⟩,
    ⟨56, 128, 1, 825, 828, 1940, 1944, 11313, 6958750961, 2939⟩,
    ⟨56, 131, 1, 848, 851, 1915, 1920, 11445, 6786938788, 2800⟩,
    ⟨56, 137, 1, 893, 896, 1867, 1871, 11704, 6468860669, 2524⟩,
    ⟨56, 139, 1, 908, 911, 1851, 1855, 11789, 6366182511, 2439⟩,
    ⟨56, 149, 1, 977, 980, 1776, 1780, 12206, 5906184360, 2066⟩,
    ⟨56, 151, 1, 990, 993, 1762, 1766, 12288, 5824073891, 2001⟩,
    ⟨56, 157, 1, 1029, 1032, 1720, 1724, 12529, 5584528456, 1814⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block4_check :
    quarterUpperRows56Block4.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
