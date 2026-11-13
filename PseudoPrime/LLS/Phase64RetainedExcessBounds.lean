/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64RamifiedExcessBounds

/-! # Retain the rational aggregate precision in ramified excess bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: arbitrary rational caps for the retained primes and their weighted
aggregate upper bound e. Claim: the actual ramified excess is at most e.
Compare local costs and logarithms before summing. Role: preserve precision
without repeating the local real-cost proof for each aggregate constant. -/
theorem phase64_ramified_excess_le_of_caps (caps : ℕ → ℚ) {x : ℝ} {e : ℚ}
    (hlocal :
      ∀ p ∈ phase64LocalPrimes,
        Analysis.finiteSignedRamifiedCost Analysis.phaseResolvent64Coefficients p x ≤ (caps p : ℝ))
    (hcap :
      (phase64LocalPrimes.map (fun p ↦ phase64LocalLogUpper p * max (caps p - 3 / 100) 0)).sum ≤
        e) :
    phase64RamifiedExcess x ≤ (e : ℝ) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr hcap
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul, Rat.cast_max,
    Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hc
  have hn : phase64LocalPrimes.Nodup := by decide +kernel
  dsimp only [phase64RamifiedExcess]
  rw [← phase64_local_prime_set_eq]
  calc
    _ ≤
        ∑ p ∈ phase64LocalPrimes.toFinset,
          (phase64LocalLogUpper p : ℝ) * max ((caps p : ℝ) - 3 / 100) 0 :=
      by
      apply Finset.sum_le_sum
      intro p hp
      have hm := List.mem_toFinset.mp hp
      have hs := max_le_max_right 0 (sub_le_sub_right (hlocal p hm) (3 / 100 : ℝ))
      exact
        (mul_le_mul_of_nonneg_left hs (Real.log_natCast_nonneg p)).trans
          (mul_le_mul_of_nonneg_right (phase64_local_real_log_le hm) (le_max_right _ _))
    _ = _ := List.sum_toFinset _ hn
    _ ≤ (e : ℝ) := hc

end PseudoPrime.LLS
