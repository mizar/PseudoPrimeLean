/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64RamifiedIntervalCertificate

/-! # A real bound for the complete 24-prime ramified excess -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Every certified local ratio interval contains the actual negative real
power. Cast the exact endpoint powers and apply the twentieth-root comparison. -/
theorem phase64_local_real_ratio_interval {p : ℕ} (hp : p ∈ phase64LocalPrimes) (ab : ℚ × ℚ)
    (hab : ab ∈ phaseResolvent64Coefficients) :
    (phase64LocalRatioInterval p ab.1).1 ≤ (p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (p : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (phase64LocalRatioInterval p ab.1).2 := by
  have hc := List.forall_iff_forall_mem.mp phase64_local_interval_checks p hp
  obtain ⟨hl, hlu, _, he, hlo, hhi⟩ := List.forall_iff_forall_mem.mp hc.2.1 ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_le (K := ℝ)).mpr hlu
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one, Rat.cast_zero] at hlR huR hloR hhiR heR
  have hexp : -(gammaSmallPrimeRatioExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  simpa only [hexp] using
    gamma_rpow_neg_twentieth_interval (by exact_mod_cast Nat.zero_lt_of_lt hc.1) hlR (hlR.trans huR)
      (gammaSmallPrimeRatioExponent ab.1) hloR hhiR

/-- At each of the 24 local primes, the full signed Euler progression cost
is bounded by its rational node sum. Select endpoints by coefficient sign
before adding the real inequalities. -/
theorem phase64_local_real_euler_cost_le {p : ℕ} (hp : p ∈ phase64LocalPrimes) :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients p 1 1 ≤
      (phase64LocalEulerUpper p : ℝ) := by
  have hc := List.forall_iff_forall_mem.mp phase64_local_interval_checks p hp
  have hs :=
    List.sum_le_sum
      (fun ab hab ↦
        signed_geometric_node_le_interval (c := ab.2)
          (List.forall_iff_forall_mem.mp hc.2.1 ab hab).1
          (phase64_local_real_ratio_interval hp ab hab).1
          (phase64_local_real_ratio_interval hp ab hab).2
          (List.forall_iff_forall_mem.mp hc.2.1 ab hab).2.2.1 (by norm_num only : 0 < (1 : ℕ)))
  simpa only [finiteSignedPrimeProgressionCost, phase64LocalEulerUpper, pow_one, Rat.cast_list_sum,
    List.map_map, Function.comp_def] using hs

/-- For each local prime and every scale from 1600 to 1660, the exact signed
ramified cost is below its rounded rational allowance. The full negative cutoff
tail is nonpositive; the finite exponential prefix uses reciprocal Taylor bounds. -/
theorem phase64_local_real_signed_cost_le {p : ℕ} (hp : p ∈ phase64LocalPrimes) {x : ℝ}
    (hlo : 1600 ≤ x) (hhi : x ≤ 1660) :
    finiteSignedRamifiedCost phaseResolvent64Coefficients p x ≤ (phase64LocalCostUpper p : ℝ) := by
  have hc := List.forall_iff_forall_mem.mp phase64_local_interval_checks p hp
  have hcut := (Rat.cast_le (K := ℝ)).mpr hc.2.2.1
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow] at hcut
  have hr :=
    prime_ramified_series_le_exp_prefix hc.1 (by norm_num only : (0 : ℝ) < 1600) hlo hhi
      (phase64LocalPowerCount p)
      (by
        norm_num only; exact hcut)
  rw [show Real.sqrt (1600 : ℝ) = 40 by
      rw [show (1600 : ℝ) = 40 ^ 2 by norm_num only,
        Real.sqrt_sq (by norm_num only : (0 : ℝ) ≤ 40)]] at hr
  have ht :=
    div_le_div_of_nonneg_right
      (prime_exp_prefix_upper_valid p (by norm_num only : (0 : ℚ) < 1660)
        (phase64LocalPowerCount p))
      (by norm_num only : (0 : ℝ) ≤ 40)
  have hcost := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hcost
  have he := phase64_local_real_euler_cost_le hp
  dsimp only [finiteSignedRamifiedCost]
  linarith only [he, hr, ht, hcost]

/-- The actual logarithm of each local prime is at most its certified rational
upper endpoint. Apply the logarithm interval soundness theorem to the kernel data. -/
theorem phase64_local_real_log_le {p : ℕ} (hp : p ∈ phase64LocalPrimes) :
    Real.log p ≤ (phase64LocalLogUpper p : ℝ) := by
  have hc := List.forall_iff_forall_mem.mp phase64_local_interval_checks p hp
  have h := (rationalLogIntervalCheck_sound hc.2.2.2.1).2
  simpa only [Rat.cast_natCast] using h

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

end PseudoPrime.Analysis
