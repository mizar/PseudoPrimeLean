/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64RamifiedExcessBounds
public import PseudoPrime.Analysis.Phase64Ramified1700Certificate

/-! # Parametric local costs and a ramified excess cap through scale 1700 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a retained prime, positive rational upper scale and rational cost cap.
Claim: the cutoff and finite Taylor allowance bound the real signed local cost
throughout 1600 <= x <= hi. Compare the Euler term and prefix separately.
Role: reuse one real proof for different compact rational scale certificates. -/
theorem phase64_local_real_signed_cost_le_of_cap {p : ℕ} (hp : p ∈ phase64LocalPrimes) {x : ℝ}
    {hi cap : ℚ} (hlo : 1600 ≤ x) (hhi : x ≤ (hi : ℝ)) (hpos : 0 < hi)
    (hcutQ : (99 / 40 : ℚ) * hi ≤ (p : ℚ) ^ (phase64LocalPowerCount p + 1))
    (hcap :
      phase64LocalEulerUpper p + primeExpPrefixUpper p hi (phase64LocalPowerCount p) / 40 ≤ cap) :
    finiteSignedRamifiedCost phaseResolvent64Coefficients p x ≤ (cap : ℝ) := by
  have hc := List.forall_iff_forall_mem.mp phase64_local_interval_checks p hp
  have hcut := (Rat.cast_le (K := ℝ)).mpr hcutQ
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow] at hcut
  have hr :=
    prime_ramified_series_le_exp_prefix hc.1 (by norm_num only : (0 : ℝ) < 1600) hlo hhi
      (phase64LocalPowerCount p) hcut
  rw [show Real.sqrt (1600 : ℝ) = 40 by
      rw [show (1600 : ℝ) = 40 ^ 2 by norm_num only,
        Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 40)]] at hr
  have ht :=
    div_le_div_of_nonneg_right (prime_exp_prefix_upper_valid p hpos (phase64LocalPowerCount p))
      (by norm_num only : (0 : ℝ) ≤ 40)
  have hcost := (Rat.cast_le (K := ℝ)).mpr hcap
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hcost
  have he := phase64_local_real_euler_cost_le hp
  dsimp only [finiteSignedRamifiedCost]
  linarith only [he, hr, ht, hcost]

/-- Claim: all retained primes meet the cutoff and local allowance at scale 1700.
Join the three checked lists; no prime-power table is generated.
Role: supply the hypotheses of the parametric real local bound. -/
theorem phase64_local_1700_checks :
    phase64LocalPrimes.Forall
      (fun (p : ℕ) ↦
        (99 / 40 : ℚ) * 1700 ≤ (p : ℚ) ^ (phase64LocalPowerCount p + 1) ∧
          phase64LocalEulerUpper p + primeExpPrefixUpper p 1700 (phase64LocalPowerCount p) / 40 ≤
            phase64LocalCostUpper1700 p) := by
  have he :
    phase64LocalPrimes =
      ([3, 5, 7, 11, 13, 17, 19, 23] : List ℕ) ++ [29, 31, 37, 41, 43, 47, 53, 59] ++
        [61, 67, 71, 73, 79, 83, 89, 97] := by
    decide +kernel
  rw [he, List.forall_append, List.forall_append]
  exact ⟨⟨phase64_local_1700_check1, phase64_local_1700_check2⟩, phase64_local_1700_check3⟩

/-- Input: a retained prime and 1600 <= x <= 1700.
Claim: its real signed ramified cost is bounded by the rounded rational cap.
Apply the parametric local theorem to the checked scale-1700 data.
Role: transfer the compact certificate to the ramified excess sum. -/
theorem phase64_local_real_signed_cost_le_1700 {p : ℕ} (hp : p ∈ phase64LocalPrimes) {x : ℝ}
    (hlo : 1600 ≤ x) (hhi : x ≤ 1700) :
    finiteSignedRamifiedCost phaseResolvent64Coefficients p x ≤
      (phase64LocalCostUpper1700 p : ℝ) := by
  have hc := List.forall_iff_forall_mem.mp phase64_local_1700_checks p hp
  exact
    phase64_local_real_signed_cost_le_of_cap hp hlo hhi (by norm_num only : (0 : ℚ) < 1700) hc.1
      hc.2

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

end PseudoPrime.Analysis
