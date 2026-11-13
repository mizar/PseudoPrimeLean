/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64DyadicEulerBounds
import PseudoPrime.Analysis.Phase64EulerPrefixUpper

/-! # Table-free signed Euler prefix bounds for the phase64 candidate -/

public section

namespace PseudoPrime.Analysis

/-- The actual signed Mangoldt prefix through 500 is at least 57/20.
Apply every checked row lower bound, distinctness and nonnegativity of omitted
weights, then transfer the rational sum certificate into the reals. -/
theorem phase64_prefix_seed_lower :
    (57 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 500, finiteSignedMangoldtWeight phaseResolvent64Coefficients n := by
  have hr :=
    nonnegative_weight_prefix_le_of_rows (finiteSignedMangoldtWeight phaseResolvent64Coefficients)
      (finiteSignedMangoldtWeight_nonneg phaseResolvent64Coefficients
        (fun u hu ↦ phaseResolvent64_euler_nonneg hu))
      phase64PrefixSeedRows (fun r ↦ r.1.index) Prod.snd phase64_prefix_seed_indices_nodup
      (fun r hr ↦ by
        have h := List.forall_iff_forall_mem.mp phase64_prefix_seed_checks r hr
        exact ⟨h.2.2.2.1, h.2.2.2.2⟩)
      (fun r hr ↦ by
        have h := List.forall_iff_forall_mem.mp phase64_prefix_seed_checks r hr
        exact
          ((Rat.cast_le (K := ℝ)).mpr h.2.2.1).trans
            (r.1.signedLower_le phaseResolvent64Coefficients (by norm_num only : 0 < (20 : ℕ)) h.1
              h.2.1))
  have hc := (Rat.cast_le (K := ℝ)).mpr phase64_prefix_seed_rational_lower
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hr hc
  linarith only [hr, hc]

/-- At any real cutoff at least 500, the actual signed Mangoldt prefix is
at least 57/20. The seed prefix is a subset and every additional combined
Mangoldt weight is nonnegative. No input enumeration is involved. -/
theorem phase64_prefix_lower_of_cutoff_ge_500 {b : ℝ} (hb : 500 ≤ b) :
    (57 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, finiteSignedMangoldtWeight phaseResolvent64Coefficients n := by
  have hfloor : 500 ≤ ⌊b⌋₊ := (Nat.le_floor_iff (by linarith only [hb] : 0 ≤ b)).mpr hb
  have hsub : Finset.Ioc 0 500 ⊆ Finset.Ioc 0 ⌊b⌋₊ := fun n hn ↦
    Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hfloor⟩
  exact
    phase64_prefix_seed_lower.trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ ↦
          finiteSignedMangoldtWeight_nonneg phaseResolvent64Coefficients
            (fun u hu ↦ phaseResolvent64_euler_nonneg hu) n))

/-- The actual full signed Mangoldt prefix through 500 is at most 143/50.
Use exact prime-power support, the reused checked rows and the new upper
allowances. No additional power or logarithm data are generated. -/
theorem phase64_prefix_seed_upper :
    (∑ n ∈ Finset.Ioc 0 500, finiteSignedMangoldtWeight phaseResolvent64Coefficients n) ≤
      (143 / 50 : ℝ) := by
  have he :=
    prime_power_supported_prefix_eq_rows (finiteSignedMangoldtWeight phaseResolvent64Coefficients)
      (fun n hn ↦ by
        rw [finiteSignedMangoldtWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn,
          zero_mul])
      phase64PrefixSeedRows (fun r ↦ r.1.index) phase64_prefix_seed_indices_nodup 500
      phase64_prefix_seed_support
  have hs :=
    List.sum_le_sum
      (fun r hr ↦ by
        have hc := List.forall_iff_forall_mem.mp phase64_prefix_seed_checks r hr
        exact
          (r.1.le_signedUpper phaseResolvent64Coefficients (by norm_num only : 0 < (20 : ℕ)) hc.1
                hc.2.1).trans
            ((Rat.cast_le (K := ℝ)).mpr
              (List.forall_iff_forall_mem.mp phase64_prefix_upper_checks r hr)))
  have hb := (Rat.cast_le (K := ℝ)).mpr phase64_prefix_rational_upper
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at hs hb
  rw [he]
  linarith only [hs, hb]

end PseudoPrime.Analysis
