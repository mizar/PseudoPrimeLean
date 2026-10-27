/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampMonotonicity
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts

/-! # Monotonicity of the unnormalized ramp Mangoldt sum -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- At every real scale the finite ramp Mangoldt sum is nonnegative.
Each Mangoldt and ramp factor is nonnegative; use this for normalization bounds. -/
theorem exponentialRampMangoldtSum_nonneg (x : ℝ) : 0 ≤ exponentialRampMangoldtSum x := by
  exact
    Finset.sum_nonneg
      (fun n hn ↦
        mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
          (Analysis.exponentialRampWeight_bounds _).1)

/-- For positive ordered scales the unnormalized ramp Mangoldt sum increases.
Compare the weights on the smaller support and add only nonnegative terms.
This transfers a single lower endpoint bound to a continuous scale interval. -/
theorem exponentialRampMangoldtSum_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    exponentialRampMangoldtSum a ≤ exponentialRampMangoldtSum b := by
  have hcut : Finset.Ioc 0 ⌊a * (99 / 40)⌋₊ ⊆ Finset.Ioc 0 ⌊b * (99 / 40)⌋₊ :=
    Finset.Ioc_subset_Ioc_right (Nat.floor_mono (mul_le_mul_of_nonneg_right hab (by norm_num only)))
  have h :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊a * (99 / 40)⌋₊)
      (fun n hn ↦
        mul_le_mul_of_nonneg_left
          (Analysis.exponentialRampWeight_antitone
            (div_le_div_of_nonneg_left (Nat.cast_nonneg n) ha hab))
          (ArithmeticFunction.vonMangoldt_nonneg (n := n)))
  exact
    h.trans
      (Finset.sum_le_sum_of_subset_of_nonneg hcut
        (fun n hn hna ↦
          mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
            (Analysis.exponentialRampWeight_bounds _).1))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
