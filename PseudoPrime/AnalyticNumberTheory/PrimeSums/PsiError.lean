/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.PrimeSums.WeightedMangoldt
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogShiftStencilBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-! # Unconditional second-order Chebyshev psi error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.PrimeSums

/-- A nonnegative fourth-order weighted-sum bound at a point between x/2 and 2*x
transfers to the common envelope 32*B*x/log(x)^4 when x is positive and log x at least two.
Compare logarithms using log(x/2), then compare positive fourth-power denominators.
This gives one error budget at all three finite-difference stencil points. -/
theorem logWeighted_local_fourth_bound {B x y : ℝ} (hB : 0 ≤ B) (hx : 0 < x)
    (hl : 2 ≤ Real.log x) (hy : x / 2 ≤ y) (hy2 : y ≤ 2 * x)
    (hb : |Arithmetic.logWeightedMangoldtSum y - y| ≤
      B * y / Real.log y ^ 4) :
    |Arithmetic.logWeightedMangoldtSum y - y| ≤
      32 * B * x / Real.log x ^ 4 := by
  have hy0 : 0 < y := (half_pos hx).trans_le hy
  have hl0 : 0 < Real.log x := (by norm_num only : (0 : ℝ) < 2).trans_le hl
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num only)
    norm_num only at h
    exact h
  have hly : Real.log x / 2 ≤ Real.log y := by
    have h := Real.log_le_log (half_pos hx) hy
    rw [Real.log_div hx.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at h
    linarith only [h, htwo, hl]
  have hden : (Real.log x / 2) ^ 4 ≤ Real.log y ^ 4 :=
    pow_le_pow_left₀ (half_pos hl0).le hly 4
  calc
    _ ≤ B * y / Real.log y ^ 4 := hb
    _ ≤ B * y / (Real.log x / 2) ^ 4 :=
      div_le_div_of_nonneg_left (mul_nonneg hB hy0.le) (pow_pos (half_pos hl0) 4) hden
    _ ≤ B * (2 * x) / (Real.log x / 2) ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 hB)
        (pow_nonneg (half_pos hl0).le 4)
    _ = _ := by ring

/-- Chebyshev psi satisfies the eventual second-order error bound unconditionally.
Use the proved fourth-order weighted Mangoldt estimate at x and x plus or minus
x/log(x)^2. The existing three-point secant bound then gives constant 1+128*B.
This discharges the arithmetic psi input to the general L-value criteria without RH. -/
theorem psiSecondOrderBound_unconditional :
    Arithmetic.PsiSecondOrderBound := by
  obtain ⟨B, hB, hb⟩ := exists_logWeighted_fourth_order
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hb
  refine ⟨1 + 128 * B, by linarith only [hB], ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2 * X),
    Filter.eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually
      (Filter.eventually_ge_atTop (2 : ℝ))] with x hxX hx hl
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := (by norm_num only : (0 : ℝ) < 2).trans_le hl
  let h := x / Real.log x ^ 2
  let E := 32 * B * x / Real.log x ^ 4
  have hh : 0 < h := div_pos hx0 (pow_pos hl0 2)
  have hle : h ≤ x / 4 := by
    have hd : (4 : ℝ) ≤ Real.log x ^ 2 := by nlinarith only [hl, sq_nonneg (Real.log x - 2)]
    exact div_le_div_of_nonneg_left hx0.le (by norm_num only) hd
  have hE : 0 ≤ E := div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hB) hx0.le)
    (pow_nonneg hl0.le 4)
  have hb' : ∀ y : ℝ, x / 2 ≤ y → y ≤ 2 * x →
      |Arithmetic.logWeightedMangoldtSum y - y| ≤ E := by
    intro y hy hy2
    exact logWeighted_local_fourth_bound hB hx0 hl hy hy2 (hX y (by linarith only [hy, hxX]))
  have hL := hb' (x - h) (by linarith only [hle, hx0]) (by linarith only [hh, hx0])
  have hT := hb' x (by linarith only [hx0]) (by linarith only [hx0])
  have hR := hb' (x + h) (by linarith only [hh, hx0]) (by linarith only [hle, hx0])
  have hp := Arithmetic.psi_error_le_of_log_shift_stencil
    (c := 0) (b := x) (by norm_num only : (0 : ℝ) ≤ 0) hh
    (by linarith only [hle, hx0]) le_rfl
    (by simpa only [zero_mul, add_zero] using hL)
    (by simpa only [zero_mul, add_zero] using hT)
    (by simpa only [zero_mul, add_zero] using hR)
  rw [add_zero] at hp
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show x + h ≤ 2 * x by linarith only [hle, hx0])
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hE)) hh.le
  have he : h + 2 * E * (2 * x) / h = (1 + 128 * B) * x / Real.log x ^ 2 := by
    dsimp only [h, E]
    field_simp (disch := first | exact hx0.ne' | exact hl0.ne')
    ring
  exact hp.trans ((add_le_add (le_refl h) hm).trans_eq he)

end PseudoPrime.AnalyticNumberTheory.PrimeSums
