/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerCertificate

/-! # Additional Euler prefix block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 6. -/
def target028ExtraData6 : ℕ → RefinedEulerAtom
  | 1861 => ⟨1861, 1, 7528867 / 1000000, 7528872 / 1000000, 0⟩
  | 1867 => ⟨1867, 1, 7532086 / 1000000, 7532091 / 1000000, 0⟩
  | 1871 => ⟨1871, 1, 7534226 / 1000000, 7534231 / 1000000, 0⟩
  | 1873 => ⟨1873, 1, 7535294 / 1000000, 7535299 / 1000000, 0⟩
  | 1877 => ⟨1877, 1, 7537428 / 1000000, 7537433 / 1000000, 0⟩
  | 1879 => ⟨1879, 1, 7538492 / 1000000, 7538497 / 1000000, 0⟩
  | 1889 => ⟨1889, 1, 7543800 / 1000000, 7543805 / 1000000, 0⟩
  | 1901 => ⟨1901, 1, 7550133 / 1000000, 7550138 / 1000000, 0⟩
  | 1907 => ⟨1907, 1, 7553284 / 1000000, 7553289 / 1000000, 0⟩
  | 1913 => ⟨1913, 1, 7556425 / 1000000, 7556430 / 1000000, 0⟩
  | 1931 => ⟨1931, 1, 7565791 / 1000000, 7565796 / 1000000, 0⟩
  | 1933 => ⟨1933, 1, 7566826 / 1000000, 7566831 / 1000000, 0⟩
  | 1949 => ⟨1949, 1, 7575069 / 1000000, 7575074 / 1000000, 0⟩
  | 1951 => ⟨1951, 1, 7576095 / 1000000, 7576100 / 1000000, 0⟩
  | 1973 => ⟨1973, 1, 7587308 / 1000000, 7587313 / 1000000, 0⟩
  | 1979 => ⟨1979, 1, 7590344 / 1000000, 7590349 / 1000000, 0⟩
  | 1987 => ⟨1987, 1, 7594379 / 1000000, 7594384 / 1000000, 0⟩
  | 1993 => ⟨1993, 1, 7597394 / 1000000, 7597399 / 1000000, 0⟩
  | 1997 => ⟨1997, 1, 7599399 / 1000000, 7599404 / 1000000, 0⟩
  | 1999 => ⟨1999, 1, 7600400 / 1000000, 7600405 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 6. -/
def target028ExtraSet6 : Finset ℕ :=
  {
    1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901,
    1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979,
    1987, 1993, 1997, 1999
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 6 row passes the Euler atom checker. -/
theorem target028_extra_check6 :
    ∀ n ∈ target028ExtraSet6, refinedEulerAtomCheck 24 n (target028ExtraData6 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 6 lie within its stated endpoints. -/
theorem target028_extra_range6 : ∀ n ∈ target028ExtraSet6, 1849 < n ∧ n ≤ 1999 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
