/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerSeries
import PseudoPrime.Analysis.GammaEulerSeed100

/-! # Scalar Euler prefix bound certified by the private seed rows -/

public section

namespace PseudoPrime.Analysis

/-- Claim: the actual signed Mangoldt Euler prefix through 100 is at least 317/100.
Proof: sum the validated prime-power rows and use nonnegativity on omitted inputs.
Role: provide the small-cutoff input for analytic prefix transport, without RH. -/
theorem gamma_euler_prefix_lower_100 :
    (317 / 100 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 100, gammaResolventMangoldtWeight m := by
  have h :=
    gamma_finite_row_block_lower smallSeedRows 0 100 small_seed_primes small_seed_rows_check
      small_seed_distinct small_seed_members
  have hs := (Rat.cast_le (K := ℝ)).mpr small_seed_sum_lower
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hs
  exact hs.trans h

end PseudoPrime.Analysis
