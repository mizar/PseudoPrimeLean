/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data

/-! # Primality checks for the additional prime labels -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 1 passes its primality and bound checks. -/
theorem primeSeed1849Extra_checked1 :
    ((primeSeed1849Extra.drop 0).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 2 passes its primality and bound checks. -/
theorem primeSeed1849Extra_checked2 :
    ((primeSeed1849Extra.drop 45).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 3 passes its primality and bound checks. -/
theorem primeSeed1849Extra_checked3 :
    ((primeSeed1849Extra.drop 90).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 4 passes its primality and bound checks. -/
theorem primeSeed1849Extra_checked4 :
    ((primeSeed1849Extra.drop 135).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 5 passes its primality and bound checks. -/
theorem primeSeed1849Extra_checked5 :
    ((primeSeed1849Extra.drop 180).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- The complete supply is duplicate-free and its positive weights match. -/
theorem primeSeed1849_labels :
    primeSeed1849Primes.Nodup ∧
      primeSeed1849Primes.map primeSeed1849Weight = primeSeed1849Weights ∧
      ∀ p ∈ primeSeed1849Primes, 0 < primeSeed1849Weight p := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
