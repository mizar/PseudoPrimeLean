/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerCertificate

/-! # Additional Euler prefix block 7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 7. -/
def target028ExtraData7 : ℕ → RefinedEulerAtom
  | 2003 => ⟨2003, 1, 7602399 / 1000000, 7602404 / 1000000, 0⟩
  | 2011 => ⟨2011, 1, 7606385 / 1000000, 7606390 / 1000000, 0⟩
  | 2017 => ⟨2017, 1, 7609364 / 1000000, 7609369 / 1000000, 0⟩
  | 2027 => ⟨2027, 1, 7614310 / 1000000, 7614315 / 1000000, 0⟩
  | 2029 => ⟨2029, 1, 7615296 / 1000000, 7615301 / 1000000, 0⟩
  | 2039 => ⟨2039, 1, 7620212 / 1000000, 7620217 / 1000000, 0⟩
  | 2048 => ⟨2, 11, 693145 / 1000000, 693150 / 1000000, 0⟩
  | 2053 => ⟨2053, 1, 7627055 / 1000000, 7627060 / 1000000, 0⟩
  | 2063 => ⟨2063, 1, 7631914 / 1000000, 7631919 / 1000000, 0⟩
  | 2069 => ⟨2069, 1, 7634818 / 1000000, 7634823 / 1000000, 0⟩
  | 2081 => ⟨2081, 1, 7640601 / 1000000, 7640606 / 1000000, 0⟩
  | 2083 => ⟨2083, 1, 7641562 / 1000000, 7641567 / 1000000, 0⟩
  | 2087 => ⟨2087, 1, 7643480 / 1000000, 7643485 / 1000000, 0⟩
  | 2089 => ⟨2089, 1, 7644438 / 1000000, 7644443 / 1000000, 0⟩
  | 2099 => ⟨2099, 1, 7649214 / 1000000, 7649219 / 1000000, 0⟩
  | 2111 => ⟨2111, 1, 7654915 / 1000000, 7654920 / 1000000, 0⟩
  | 2113 => ⟨2113, 1, 7655862 / 1000000, 7655867 / 1000000, 0⟩
  | 2129 => ⟨2129, 1, 7663405 / 1000000, 7663410 / 1000000, 0⟩
  | 2131 => ⟨2131, 1, 7664344 / 1000000, 7664349 / 1000000, 0⟩
  | 2137 => ⟨2137, 1, 7667156 / 1000000, 7667161 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 7. -/
def target028ExtraSet7 : Finset ℕ :=
  {
    2003, 2011, 2017, 2027, 2029, 2039, 2048, 2053,
    2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111,
    2113, 2129, 2131, 2137
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 7 row passes the Euler atom checker. -/
theorem target028_extra_check7 :
    ∀ n ∈ target028ExtraSet7, refinedEulerAtomCheck 24 n (target028ExtraData7 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 7 lie within its stated endpoints. -/
theorem target028_extra_range7 : ∀ n ∈ target028ExtraSet7, 1999 < n ∧ n ≤ 2137 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
