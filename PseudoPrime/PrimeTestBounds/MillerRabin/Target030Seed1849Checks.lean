/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed1849Data

/-! # Primality checks for the additional prime labels -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 1 passes its primality and bound checks. -/
theorem target030Extra1849_checked1 :
    ((target030Extra1849.drop 0).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 2 passes its primality and bound checks. -/
theorem target030Extra1849_checked2 :
    ((target030Extra1849.drop 45).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 3 passes its primality and bound checks. -/
theorem target030Extra1849_checked3 :
    ((target030Extra1849.drop 90).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 4 passes its primality and bound checks. -/
theorem target030Extra1849_checked4 :
    ((target030Extra1849.drop 135).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- Additional prime-label chunk 5 passes its primality and bound checks. -/
theorem target030Extra1849_checked5 :
    ((target030Extra1849.drop 180).take 45).all (fun p ↦ decide (p.Prime ∧ 373 < p ∧ p ≤ 1849)) =
      true := by
  decide +kernel

set_option maxRecDepth 32768 in
/-- The complete supply is duplicate-free and its positive weights match. -/
theorem target030Seed1849_labels :
    target030Seed1849Primes.Nodup ∧
      target030Seed1849Primes.map target030Seed1849Weight = target030Seed1849Weights ∧
      ∀ p ∈ target030Seed1849Primes, 0 < target030Seed1849Weight p := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
