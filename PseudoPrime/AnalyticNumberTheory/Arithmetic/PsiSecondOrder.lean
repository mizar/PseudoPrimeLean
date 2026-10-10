/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-! Reduction of quantitative prime-number errors to the second-order logarithmic scale. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A stretched exponential prime-number error implies `PsiSecondOrderBound`.
Assume positive `c` and `a` and the Big-O bound with weight
`x * exp (-c * (log x)^a)`. Choose its nonnegative constant and use the eventual
inverse-square logarithmic bound. This accepts quantitative PNT results without RH assumptions. -/
theorem psiSecondOrderBound_of_exp_log_rpow {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (h :
      Asymptotics.IsBigO Filter.atTop (fun x : ℝ ↦ Chebyshev.psi x - x)
        (fun x ↦ x * Real.exp (-c * (Real.log x) ^ a))) :
    PsiSecondOrderBound := by
  obtain ⟨B, hB, hb⟩ := h.exists_nonneg
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb.bound, Analysis.eventually_exp_neg_log_rpow_le_inv_log_sq hc ha,
    Filter.eventually_ge_atTop (0 : ℝ)] with x hx hd hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 (Real.exp_pos _).le)] at hx
  calc
    |Chebyshev.psi x - x| ≤ B * (x * Real.exp (-c * (Real.log x) ^ a)) := hx
    _ ≤ B * (x * (1 / (Real.log x) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hx0) hB
    _ = B * x / (Real.log x) ^ 2 := by rw [mul_one_div, mul_div_assoc]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
