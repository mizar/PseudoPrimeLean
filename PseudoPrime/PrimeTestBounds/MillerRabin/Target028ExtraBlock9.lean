/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock8

/-! # Additional Euler prefix block 9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 9. -/
def target028ExtraData9 : ℕ → RefinedEulerAtom
  | 2287 => ⟨2287, 1, 7734994 / 1000000, 7734999 / 1000000, 0⟩
  | 2293 => ⟨2293, 1, 7737614 / 1000000, 7737619 / 1000000, 0⟩
  | 2297 => ⟨2297, 1, 7739357 / 1000000, 7739362 / 1000000, 0⟩
  | 2309 => ⟨2309, 1, 7744567 / 1000000, 7744572 / 1000000, 0⟩
  | 2311 => ⟨2311, 1, 7745433 / 1000000, 7745438 / 1000000, 0⟩
  | 2333 => ⟨2333, 1, 7754908 / 1000000, 7754913 / 1000000, 0⟩
  | 2339 => ⟨2339, 1, 7757476 / 1000000, 7757481 / 1000000, 0⟩
  | 2341 => ⟨2341, 1, 7758331 / 1000000, 7758336 / 1000000, 0⟩
  | 2347 => ⟨2347, 1, 7760891 / 1000000, 7760896 / 1000000, 0⟩
  | 2351 => ⟨2351, 1, 7762594 / 1000000, 7762599 / 1000000, 0⟩
  | 2357 => ⟨2357, 1, 7765142 / 1000000, 7765147 / 1000000, 0⟩
  | 2371 => ⟨2371, 1, 7771065 / 1000000, 7771070 / 1000000, 0⟩
  | 2377 => ⟨2377, 1, 7773592 / 1000000, 7773597 / 1000000, 0⟩
  | 2381 => ⟨2381, 1, 7775273 / 1000000, 7775278 / 1000000, 0⟩
  | 2383 => ⟨2383, 1, 7776113 / 1000000, 7776118 / 1000000, 0⟩
  | 2389 => ⟨2389, 1, 7778628 / 1000000, 7778633 / 1000000, 0⟩
  | 2393 => ⟨2393, 1, 7780301 / 1000000, 7780306 / 1000000, 0⟩
  | 2399 => ⟨2399, 1, 7782805 / 1000000, 7782810 / 1000000, 0⟩
  | 2401 => ⟨7, 4, 1945908 / 1000000, 1945913 / 1000000, 0⟩
  | 2411 => ⟨2411, 1, 7787794 / 1000000, 7787799 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 9. -/
def target028ExtraSet9 : Finset ℕ :=
  {
    2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341,
    2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389,
    2393, 2399, 2401, 2411
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 9 row passes the Euler atom checker. -/
theorem target028_extra_check9 :
    ∀ n ∈ target028ExtraSet9, refinedEulerAtomCheck 24 n (target028ExtraData9 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 9 lie within its stated endpoints. -/
theorem target028_extra_range9 : ∀ n ∈ target028ExtraSet9, 2281 < n ∧ n ≤ 2411 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
