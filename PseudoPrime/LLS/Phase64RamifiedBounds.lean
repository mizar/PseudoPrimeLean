/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64RamifiedTailBounds
import PseudoPrime.LLS.Phase64Ramified1700Bounds
import PseudoPrime.LLS.Phase64RetainedExcessBounds

/-! Table-free bounds for the phase 64 ramified excess. -/

public section

namespace PseudoPrime.LLS

/-- On the entire scale interval 1600 to 1660, the fixed signed ramified
excess is at most 13/5. Compare all 24 real terms with rational upper allowances
and use the checked small-denominator sum. No sampled-scale or floating-point
premise remains. -/
theorem phase64_ramified_excess_le_thirteen_fifths {x : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1660) :
    phase64RamifiedExcess x ≤ (13 / 5 : ℝ) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_local_excess_upper_check
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul, Rat.cast_max,
    Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hc
  have hn : phase64LocalPrimes.Nodup := by decide +kernel
  dsimp only [phase64RamifiedExcess]
  rw [← phase64_local_prime_set_eq]
  calc
    _ ≤
        ∑ p ∈ phase64LocalPrimes.toFinset,
          (phase64LocalLogUpper p : ℝ) * max ((phase64LocalCostUpper p : ℝ) - 3 / 100) 0 :=
      by
      apply Finset.sum_le_sum
      intro p hp
      have hm := List.mem_toFinset.mp hp
      have hs :=
        max_le_max_right 0
          (sub_le_sub_right (phase64_local_real_signed_cost_le hm hlo hhi) (3 / 100 : ℝ))
      exact
        (mul_le_mul_of_nonneg_left hs (Real.log_natCast_nonneg p)).trans
          (mul_le_mul_of_nonneg_right (phase64_local_real_log_le hm) (le_max_right _ _))
    _ = _ := List.sum_toFinset _ hn
    _ ≤ (13 / 5 : ℝ) := hc

/-- Input: 1600 <= x <= 1700. Claim: the total ramified excess is at most 13/5.
Compare the 24 local costs and logarithms with rational upper bounds, then
apply the checked aggregate inequality. Role: preserve the scalar Jacobi budget
on the enlarged scale interval without additional endpoint Mangoldt sums. -/
theorem phase64_ramified_excess_le_thirteen_fifths_1700 {x : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1700) :
    phase64RamifiedExcess x ≤ (13 / 5 : ℝ) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_local_1700_check0
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul, Rat.cast_max,
    Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hc
  have hn : phase64LocalPrimes.Nodup := by decide +kernel
  dsimp only [phase64RamifiedExcess]
  rw [← phase64_local_prime_set_eq]
  calc
    _ ≤
        ∑ p ∈ phase64LocalPrimes.toFinset,
          (phase64LocalLogUpper p : ℝ) * max ((phase64LocalCostUpper1700 p : ℝ) - 3 / 100) 0 :=
      by
      apply Finset.sum_le_sum
      intro p hp
      have hm := List.mem_toFinset.mp hp
      have hs :=
        max_le_max_right 0
          (sub_le_sub_right (phase64_local_real_signed_cost_le_1700 hm hlo hhi) (3 / 100 : ℝ))
      exact
        (mul_le_mul_of_nonneg_left hs (Real.log_natCast_nonneg p)).trans
          (mul_le_mul_of_nonneg_right (phase64_local_real_log_le hm) (le_max_right _ _))
    _ = _ := List.sum_toFinset _ hn
    _ ≤ (13 / 5 : ℝ) := hc

/-- Input: 1600 <= x <= 1660. Claim: the ramified excess is at most 2503/1000.
Reuse the existing 24 local caps and check their small rational aggregate.
Role: recover 97/1000 of slack previously lost by rounding the excess to 13/5. -/
theorem phase64_ramified_excess_le_2503 {x : ℝ} (hlo : 1600 ≤ x) (hhi : x ≤ 1660) :
    phase64RamifiedExcess x ≤ (2503 / 1000 : ℝ) := by
  have hc :
    (phase64LocalPrimes.map
          (fun p ↦ phase64LocalLogUpper p * max (phase64LocalCostUpper p - 3 / 100) 0)).sum ≤
      (2503 / 1000 : ℚ) := by
    decide +kernel
  have he :=
    phase64_ramified_excess_le_of_caps phase64LocalCostUpper
      (fun p hp ↦ phase64_local_real_signed_cost_le hp hlo hhi) hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  exact he

end PseudoPrime.LLS
