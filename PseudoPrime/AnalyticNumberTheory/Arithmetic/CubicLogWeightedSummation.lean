/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogWeightedSummation

/-! # Finite cubic smoothing of the logarithmic Mangoldt sum -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The unnormalized cubic-gap Mangoldt sum through a real cutoff x.
Its weight is (1-(n/x)³)/3 on positive integer indices through floor x.
This is the principal arithmetic input for the h=3 reciprocal-gap kernel. -/
noncomputable def cubicGapMangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * (1 - ((n : ℝ) / x) ^ 3) / 3

/-- For x ≥ 1, the cubic-gap sum is the logarithmic Mangoldt sum minus its
cubic smoothing integral from one to x. Apply the finite power-kernel identity
at sigma=-3 and simplify each integer endpoint. No RH or infinite interchange is used. -/
theorem cubicGapMangoldtSum_eq_log_integral {x : ℝ} (hx : 1 ≤ x) :
    cubicGapMangoldtSum x =
      logWeightedMangoldtSum x -
        3 / x ^ 3 * (∫ t in (1 : ℝ)..x, t ^ 2 * logWeightedMangoldtSum t) := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hi := power_logWeightedMangoldtSum_integral_eq (-3) (by norm_num only : (0 : ℝ) < 1) hx
  norm_num only [neg_neg] at hi
  simp only [Real.rpow_ofNat] at hi
  have he :
    (fun t : ℝ ↦ logWeightedMangoldtSum t * (9 * t ^ 2)) =
      (fun t : ℝ ↦ 9 * (t ^ 2 * logWeightedMangoldtSum t)) := by
    funext t
    ring
  rw [he, intervalIntegral.integral_const_mul] at hi
  have hs :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n *
          ((max 1 (n : ℝ)) ^ 3 * (1 + -3 * Real.log (max 1 (n : ℝ) / n)) -
            x ^ 3 * (1 + -3 * Real.log (x / n)))) =
      3 * x ^ 3 * logWeightedMangoldtSum x - 3 * x ^ 3 * cubicGapMangoldtSum x := by
    simp only [logWeightedMangoldtSum, logWeightedMangoldtTerm, cubicGapMangoldtSum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    rw [max_eq_right hn1, Real.log_div_self]
    field_simp [hx0]
    ring
  rw [hs] at hi
  field_simp [hx0]
  nlinarith only [hi]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
