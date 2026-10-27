/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
public import PseudoPrime.Analysis.RealLog

/-! # Short increments of logarithmically smoothed Mangoldt errors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For positive ordered cutoffs a,b and a common bound D on their
Chebyshev errors, the smoothed error increment is at most
((b-a)+D)(b-a)/a. Use nonnegative Mangoldt coefficients, logarithm tangents
and the exact finite-difference inequalities. This controls a short-ramp
increment without charging the two endpoint errors separately. -/
theorem logWeighted_error_increment_le_of_psi_bounds {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hA : |Chebyshev.psi a - a| ≤ D) (hB : |Chebyshev.psi b - b| ≤ D) :
    |(logWeightedMangoldtSum b - b) - (logWeightedMangoldtSum a - a)| ≤
      ((b - a) + D) * (b - a) / a := by
  have hb := ha.trans_le hab
  have hD := (abs_nonneg (Chebyshev.psi a - a)).trans hA
  have hpa : 0 ≤ Chebyshev.psi a := by
    rw [psi_eq_positive_sum]
    exact Finset.sum_nonneg (fun _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
  have hpb : 0 ≤ Chebyshev.psi b := by
    rw [psi_eq_positive_sum]
    exact Finset.sum_nonneg (fun _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
  have hla : Real.log (b / a) ≤ (b - a) / a := by
    rw [Real.log_div hb.ne' ha.ne']
    linarith only [Analysis.log_le_log_add_sub_div ha hb]
  have hlb : (b - a) / b ≤ Real.log (b / a) := by
    rw [Real.log_div hb.ne' ha.ne']
    have ht := Analysis.log_le_log_add_sub_div hb ha
    have he : (a - b) / b = -((b - a) / b) := by ring
    rw [he] at ht
    linarith only [ht]
  have hs := logWeightedMangoldtSum_difference_bounds ha hab
  have hma := mul_le_mul_of_nonneg_left hlb hpa
  have hmb := mul_le_mul_of_nonneg_left hla hpb
  have hna :=
    mul_le_mul_of_nonneg_right (show a - D ≤ Chebyshev.psi a by linarith only [(abs_le.mp hA).1])
      (div_nonneg (sub_nonneg.mpr hab) hb.le)
  have hnb :=
    mul_le_mul_of_nonneg_right (show Chebyshev.psi b ≤ b + D by linarith only [(abs_le.mp hB).2])
      (div_nonneg (sub_nonneg.mpr hab) ha.le)
  have hea : (a - D) * ((b - a) / b) - (b - a) = -(((b - a) + D) * (b - a) / b) := by
    field_simp [hb.ne']
    ring
  have heb : (b + D) * ((b - a) / a) - (b - a) = ((b - a) + D) * (b - a) / a := by
    field_simp [ha.ne']
    ring
  have hdiv :=
    div_le_div_of_nonneg_left
      (mul_nonneg (by linarith only [hab, hD] : 0 ≤ b - a + D) (sub_nonneg.mpr hab)) ha hab
  rw [abs_le]
  constructor
  · linarith only [hs.1, hma, hna, hea, hdiv]
  · linarith only [hs.2, hmb, hnb, heb]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
