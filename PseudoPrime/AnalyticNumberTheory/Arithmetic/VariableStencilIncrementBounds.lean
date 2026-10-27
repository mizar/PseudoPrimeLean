/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedIncrementBounds

/-! # Variable-width smoothed Mangoldt increments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a positive width h, a stencil centered at t with t-h positive, and t at most b,
a common error envelope E bounds the Chebyshev error by h+2E(b+h)/h.
Use the two smoothed secants and positivity of E. The width remains a parameter
for the subsequent short-interval increment estimate. -/
theorem psi_error_le_of_variable_stencil {t h b E : ℝ} (hh : 0 < h) (hl : 0 < t - h) (htb : t ≤ b)
    (hL : |logWeightedMangoldtSum (t - h) - (t - h)| ≤ E) (hT : |logWeightedMangoldtSum t - t| ≤ E)
    (hR : |logWeightedMangoldtSum (t + h) - (t + h)| ≤ E) :
    |Chebyshev.psi t - t| ≤ h + 2 * E * (b + h) / h := by
  have ht : 0 < t := by linarith only [hl, hh]
  have hE := (abs_nonneg (logWeightedMangoldtSum t - t)).trans hT
  have hlo :=
    (psi_bounds_of_logWeighted_error_without_log hl (by linarith only [hh] : t - h < t) hL hT).2
  have hhi :=
    (psi_bounds_of_logWeighted_error_without_log ht (by linarith only [hh] : t < t + h) hT hR).1
  rw [show t - (t - h) = h by ring] at hlo
  rw [show t + h - t = h by ring] at hhi
  have hupper : (E + E) * (t + h) / h ≤ 2 * E * (b + h) / h :=
    div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg hE (sub_nonneg.mpr htb)]) hh.le
  have hlower : (E + E) * (t - h) / h ≤ 2 * E * (b + h) / h :=
    div_le_div_of_nonneg_right
      (by nlinarith only [mul_nonneg hE (sub_nonneg.mpr htb), mul_nonneg hE hh.le]) hh.le
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, hupper, hlower]

/-- For positive ordered endpoints and a common three-point smoothed-error envelope,
choose any stencil width smaller than the left endpoint. The resulting Chebyshev
allowance controls the actual smoothed-error increment. This is the consumer of the
variable-stencil comparison and permits scale-dependent width selection. -/
theorem logWeighted_error_increment_le_of_variable_stencil {a b h E : ℝ} (hh : 0 < h)
    (ha : 0 < a - h) (hab : a ≤ b)
    (hE :
      ∀ t ∈ Set.Icc a b,
        |logWeightedMangoldtSum (t - h) - (t - h)| ≤ E ∧
          |logWeightedMangoldtSum t - t| ≤ E ∧ |logWeightedMangoldtSum (t + h) - (t + h)| ≤ E) :
    |(logWeightedMangoldtSum b - b) - (logWeightedMangoldtSum a - a)| ≤
      ((b - a) + (h + 2 * E * (b + h) / h)) * (b - a) / a := by
  have ha0 : 0 < a := by linarith only [ha, hh]
  have hEa := hE a ⟨le_rfl, hab⟩
  have hEb := hE b ⟨hab, le_rfl⟩
  have hpA := psi_error_le_of_variable_stencil hh ha hab hEa.1 hEa.2.1 hEa.2.2
  have hpB :=
    psi_error_le_of_variable_stencil hh (by linarith only [ha, hab] : 0 < b - h) le_rfl hEb.1
      hEb.2.1 hEb.2.2
  exact logWeighted_error_increment_le_of_psi_bounds ha0 hab hpA hpB

end PseudoPrime.AnalyticNumberTheory.Arithmetic
