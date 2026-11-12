/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Checks
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Checks
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Extra
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373WeightStep

/-! # Certified prime supply through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every label in the combined supply is prime and at most 1849. -/
theorem primeSeed1849_prime_supply : ∀ p ∈ primeSeed1849Primes, p.Prime ∧ p ≤ 1849 := by
  intro p hp
  change p ∈ primeSeed1849Extra ++ primeSeed373Primes at hp
  simp only [List.mem_append] at hp
  rcases hp with hnew | hold
  · exact ⟨(primeSeed1849Extra_prime p hnew).1, (primeSeed1849Extra_prime p hnew).2.2⟩
  · exact
      ⟨(primeSeed373_prime_supply p hold).1, (primeSeed373_prime_supply p hold).2.trans (by decide)⟩

/-- Each scaled weight dominates its prime label's logarithm. The added
labels use the certified logarithm of the common cutoff 1849. -/
theorem primeSeed1849_weight_bounds :
    ∀ p ∈ primeSeed1849Primes, Real.log p ≤ (primeSeed1849Weight p : ℝ) / 10 := by
  have h43 := primeSeed43_weight_step prime_seed19_weight_bounds
  have h61 := primeSeed61_weight_step h43
  have h89 := primeSeed89_weight_step h61
  have h113 := primeSeed113_weight_step h89
  have h199 := primeSeed199_weight_step h113
  have h281 := primeSeed281_weight_step h199
  have h373 := primeSeed373_weight_step h281
  exact primeSeed1849_weight_step primeSeed1849Extra_prime h373

end PseudoPrime.PrimeTestBounds.MillerRabin
