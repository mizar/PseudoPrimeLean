/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.VariableStencilIncrementBounds

/-! # Smoothed differences retaining a deterministic logarithmic correction -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For positive ordered cutoffs and nonnegative c, absolute bounds on the corrected
smoothed errors S(t)-t+c log t give logarithm-free upper and lower bounds on psi+c.
Add c log(y/x) to the exact positive-coefficient finite differences before applying the
logarithmic tangents. This keeps deterministic logarithmic drift out of the error budget. -/
theorem psi_bounds_of_log_shift_error_without_log {x y Ex Ey c : ℝ} (hc : 0 ≤ c) (hx : 0 < x)
    (hxy : x < y) (hxE : |logWeightedMangoldtSum x - x + c * Real.log x| ≤ Ex)
    (hyE : |logWeightedMangoldtSum y - y + c * Real.log y| ≤ Ey) :
    Chebyshev.psi x + c ≤ y + (Ex + Ey) * y / (y - x) ∧
      x - (Ex + Ey) * x / (y - x) ≤ Chebyshev.psi y + c := by
  have hy : 0 < y := hx.trans hxy
  have hd : 0 < y - x := sub_pos.mpr hxy
  have hlo : (y - x) / y ≤ Real.log (y / x) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [inv_div, one_sub_div hy.ne'] at h
    exact h
  have hhi : Real.log (y / x) ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [div_sub_one hx.ne'] at h
    exact h
  have h := logWeightedMangoldtSum_difference_bounds hx hxy.le
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hEx := abs_le.mp hxE
  have hEy := abs_le.mp hyE
  have hu := mul_le_mul_of_nonneg_left hlo (add_nonneg (Chebyshev.psi_nonneg x) hc)
  have hl := mul_le_mul_of_nonneg_left hhi (add_nonneg (Chebyshev.psi_nonneg y) hc)
  rw [Real.log_div hy.ne' hx.ne'] at hu hl
  have hupper : (Chebyshev.psi x + c) * (y - x) / y ≤ y - x + Ex + Ey := by
    rw [mul_div_assoc]
    linarith only [hu, h.1, hEx.1, hEy.2]
  have hlower : y - x - Ex - Ey ≤ (Chebyshev.psi y + c) * (y - x) / x := by
    rw [mul_div_assoc]
    linarith only [hl, h.2, hEx.2, hEy.1]
  have hu' := (div_le_iff₀ hy).mp hupper
  have hl' := (le_div_iff₀ hx).mp hlower
  constructor
  · apply (mul_le_mul_iff_left₀ hd).mp
    calc
      (Chebyshev.psi x + c) * (y - x) ≤ (y - x + Ex + Ey) * y := hu'
      _ = (y + (Ex + Ey) * y / (y - x)) * (y - x) := by
        simp only [add_mul, div_mul_cancel₀ _ hd.ne']
        ring
  · apply (mul_le_mul_iff_left₀ hd).mp
    calc
      (x - (Ex + Ey) * x / (y - x)) * (y - x) = (y - x - Ex - Ey) * x := by
        simp only [sub_mul, div_mul_cancel₀ _ hd.ne']
        ring
      _ ≤ (Chebyshev.psi y + c) * (y - x) := hl'

/-- For a positive stencil width, nonnegative c and a common corrected error bound E,
the Chebyshev error is at most h+2E(b+h)/h+c. Use the two corrected secants and a common
endpoint cap. The logarithmic correction is charged once as c rather than twice as c log t. -/
theorem psi_error_le_of_log_shift_stencil {t h b E c : ℝ} (hc : 0 ≤ c) (hh : 0 < h) (hl : 0 < t - h)
    (htb : t ≤ b) (hL : |logWeightedMangoldtSum (t - h) - (t - h) + c * Real.log (t - h)| ≤ E)
    (hT : |logWeightedMangoldtSum t - t + c * Real.log t| ≤ E)
    (hR : |logWeightedMangoldtSum (t + h) - (t + h) + c * Real.log (t + h)| ≤ E) :
    |Chebyshev.psi t - t| ≤ h + 2 * E * (b + h) / h + c := by
  have ht : 0 < t := by linarith only [hl, hh]
  have hE := (abs_nonneg (logWeightedMangoldtSum t - t + c * Real.log t)).trans hT
  have hlo :=
    (psi_bounds_of_log_shift_error_without_log hc hl (by linarith only [hh] : t - h < t) hL hT).2
  have hhi :=
    (psi_bounds_of_log_shift_error_without_log hc ht (by linarith only [hh] : t < t + h) hT hR).1
  rw [show t - (t - h) = h by ring] at hlo
  rw [show t + h - t = h by ring] at hhi
  have hupper : (E + E) * (t + h) / h ≤ 2 * E * (b + h) / h :=
    div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg hE (sub_nonneg.mpr htb)]) hh.le
  have hlower : (E + E) * (t - h) / h ≤ 2 * E * (b + h) / h :=
    div_le_div_of_nonneg_right
      (by nlinarith only [mul_nonneg hE (sub_nonneg.mpr htb), mul_nonneg hE hh.le]) hh.le
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, hupper, hlower, hc]

/-- For positive ordered endpoints and a common corrected three-point envelope,
the actual uncorrected smoothed-error increment satisfies the displayed bound.
Apply the corrected stencil to the two Chebyshev endpoints and the existing increment
comparison. This connects deterministic logarithmic cancellation to the short-ramp consumer. -/
theorem logWeighted_error_increment_le_of_log_shift_stencil {a b h E c : ℝ} (hc : 0 ≤ c)
    (hh : 0 < h) (ha : 0 < a - h) (hab : a ≤ b)
    (hE :
      ∀ t ∈ Set.Icc a b,
        |logWeightedMangoldtSum (t - h) - (t - h) + c * Real.log (t - h)| ≤ E ∧
          |logWeightedMangoldtSum t - t + c * Real.log t| ≤ E ∧
          |logWeightedMangoldtSum (t + h) - (t + h) + c * Real.log (t + h)| ≤ E) :
    |(logWeightedMangoldtSum b - b) - (logWeightedMangoldtSum a - a)| ≤
      ((b - a) + (h + 2 * E * (b + h) / h + c)) * (b - a) / a := by
  have ha0 : 0 < a := by linarith only [ha, hh]
  have hEa := hE a ⟨le_rfl, hab⟩
  have hEb := hE b ⟨hab, le_rfl⟩
  have hpA := psi_error_le_of_log_shift_stencil hc hh ha hab hEa.1 hEa.2.1 hEa.2.2
  have hpB :=
    psi_error_le_of_log_shift_stencil hc hh (by linarith only [ha, hab] : 0 < b - h) le_rfl hEb.1
      hEb.2.1 hEb.2.2
  exact logWeighted_error_increment_le_of_psi_bounds ha0 hab hpA hpB

end PseudoPrime.AnalyticNumberTheory.Arithmetic
