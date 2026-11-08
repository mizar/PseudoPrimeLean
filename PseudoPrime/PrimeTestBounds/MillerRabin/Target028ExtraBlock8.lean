/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock7

/-! # Additional Euler prefix block 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 8. -/
def target028ExtraData8 : ℕ → RefinedEulerAtom
  | 2141 => ⟨2141, 1, 7669026 / 1000000, 7669031 / 1000000, 0⟩
  | 2143 => ⟨2143, 1, 7669959 / 1000000, 7669964 / 1000000, 0⟩
  | 2153 => ⟨2153, 1, 7674615 / 1000000, 7674620 / 1000000, 0⟩
  | 2161 => ⟨2161, 1, 7678324 / 1000000, 7678329 / 1000000, 0⟩
  | 2179 => ⟨2179, 1, 7686619 / 1000000, 7686624 / 1000000, 0⟩
  | 2187 => ⟨3, 7, 1098610 / 1000000, 1098615 / 1000000, 0⟩
  | 2197 => ⟨13, 3, 2564947 / 1000000, 2564952 / 1000000, 0⟩
  | 2203 => ⟨2203, 1, 7697573 / 1000000, 7697578 / 1000000, 0⟩
  | 2207 => ⟨2207, 1, 7699387 / 1000000, 7699392 / 1000000, 0⟩
  | 2209 => ⟨47, 2, 3850145 / 1000000, 3850150 / 1000000, 0⟩
  | 2213 => ⟨2213, 1, 7702102 / 1000000, 7702107 / 1000000, 0⟩
  | 2221 => ⟨2221, 1, 7705710 / 1000000, 7705715 / 1000000, 0⟩
  | 2237 => ⟨2237, 1, 7712888 / 1000000, 7712893 / 1000000, 0⟩
  | 2239 => ⟨2239, 1, 7713782 / 1000000, 7713787 / 1000000, 0⟩
  | 2243 => ⟨2243, 1, 7715567 / 1000000, 7715572 / 1000000, 0⟩
  | 2251 => ⟨2251, 1, 7719127 / 1000000, 7719132 / 1000000, 0⟩
  | 2267 => ⟨2267, 1, 7726210 / 1000000, 7726215 / 1000000, 0⟩
  | 2269 => ⟨2269, 1, 7727092 / 1000000, 7727097 / 1000000, 0⟩
  | 2273 => ⟨2273, 1, 7728853 / 1000000, 7728858 / 1000000, 0⟩
  | 2281 => ⟨2281, 1, 7732367 / 1000000, 7732372 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 8. -/
def target028ExtraSet8 : Finset ℕ :=
  {
    2141, 2143, 2153, 2161, 2179, 2187, 2197, 2203,
    2207, 2209, 2213, 2221, 2237, 2239, 2243, 2251,
    2267, 2269, 2273, 2281
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 8 row passes the Euler atom checker. -/
theorem target028_extra_check8 :
    ∀ n ∈ target028ExtraSet8, refinedEulerAtomCheck 24 n (target028ExtraData8 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 8 lie within its stated endpoints. -/
theorem target028_extra_range8 : ∀ n ∈ target028ExtraSet8, 2137 < n ∧ n ≤ 2281 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
