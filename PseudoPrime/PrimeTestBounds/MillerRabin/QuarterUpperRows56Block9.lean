/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block9 : List QuarterUpperWeightRow :=
  [⟨56, 361, 3, 1862, 1865, 820, 825, 19000, 2270499831, 74⟩,
    ⟨56, 367, 3, 1879, 1882, 802, 806, 19157, 2229996460, 67⟩,
    ⟨56, 373, 3, 1895, 1898, 785, 789, 19313, 2192406935, 61⟩,
    ⟨56, 379, 3, 1911, 1914, 767, 772, 19467, 2153296660, 55⟩,
    ⟨56, 383, 3, 1921, 1924, 757, 761, 19570, 2131870999, 51⟩,
    ⟨56, 389, 3, 1937, 1940, 739, 744, 19723, 2093840623, 47⟩,
    ⟨56, 397, 3, 1957, 1960, 718, 722, 19924, 2050328445, 41⟩,
    ⟨56, 401, 3, 1967, 1970, 707, 711, 20024, 2027898423, 38⟩,
    ⟨56, 409, 3, 1987, 1990, 685, 690, 20223, 1983771832, 33⟩,
    ⟨56, 419, 3, 2011, 2014, 659, 664, 20469, 1932858505, 28⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block9_check :
    quarterUpperRows56Block9.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
