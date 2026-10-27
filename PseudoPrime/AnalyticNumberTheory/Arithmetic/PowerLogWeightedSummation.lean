/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PowerLogKernel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts

/-! # Finite double partial summation for Mangoldt power weights -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- On a positive finite cutoff interval, the actual logarithmically
weighted Mangoldt sum has an exact power-kernel integral with both endpoints.
The fixed upper integer prefix includes prime powers at the endpoint.
No RH or passage to an infinite sum is used in this finite identity. -/
theorem power_logWeightedMangoldtSum_integral_eq (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1))) =
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          ((max a (m : ℝ)) ^ (-σ) * (1 + σ * Real.log (max a (m : ℝ) / m)) -
            b ^ (-σ) * (1 + σ * Real.log (b / m))) := by
  have hi :=
    Analysis.finite_sum_power_log_integral_eq (Finset.Ioc 0 ⌊b⌋₊)
      (fun m ↦ ArithmeticFunction.vonMangoldt m) (fun m ↦ (m : ℝ)) σ ha hab
      (fun m hm ↦ Nat.cast_pos.mpr (Finset.mem_Ioc.mp hm).1)
      (fun m hm ↦ (Nat.le_floor_iff (ha.trans_le hab).le).mp (Finset.mem_Ioc.mp hm).2)
  have he :
    (∫ t in a..b, logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1))) =
      ∫ t in a..b,
        (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
            ArithmeticFunction.vonMangoldt m * Analysis.positiveLogRatio (m : ℝ) t) *
          (σ ^ 2 * t ^ (-σ - 1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have h :=
      logWeightedMangoldtSum_eq_clipped_scaled (x := (1 : ℝ)) (by norm_num only)
        (ha.trans_le ht.1).le ht.2
    simp only [one_mul, div_one] at h
    dsimp only
    rw [h]
  exact he.trans hi

end PseudoPrime.AnalyticNumberTheory.Arithmetic
