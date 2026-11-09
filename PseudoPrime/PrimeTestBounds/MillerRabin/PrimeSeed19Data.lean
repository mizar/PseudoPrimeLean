/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # First low-scale weighted count certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integer weights for the eight supplied primes up to 19, including four
small seeds. Distinct primes 17 and 19 carry the same weight. -/
def primeSeed19Weights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30]

/-- The eight primes needed by the first half-open supply cutoff. Each is
listed once, so these labels support repeated products without merging primes
that have the same logarithmic weight. -/
def primeSeed19Primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19]

/-- Integer logarithm weights for the first prime supply, scaled by ten. The
last group uses a common weight for 17 and 19, matching the existing supply
at cutoff 19. -/
def primeSeed19Weight (p : ℕ) : ℕ :=
  if p ≤ 2 then 7
  else
    if p ≤ 3 then 11
    else
      if p ≤ 5 then 17 else if p ≤ 7 then 20 else if p ≤ 11 then 24 else if p ≤ 13 then 26 else 30

/-- The first explicit prime list has no duplicate labels and maps to the
certified weight list. Kernel reduction checks the finite list. -/
theorem primeSeed19_labels :
    primeSeed19Primes.Nodup ∧
      primeSeed19Primes.map primeSeed19Weight = primeSeed19Weights ∧
      ∀ p ∈ primeSeed19Primes, 0 < primeSeed19Weight p := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
