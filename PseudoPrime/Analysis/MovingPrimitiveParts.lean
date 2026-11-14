/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Integration by parts with an integral primitive -/

public section

namespace PseudoPrime.Analysis

/-- For an interval-integrable real function and an absolutely continuous
weight with the stated derivative, integrate by parts using the moving
primitive based at the lower endpoint. The primitive has the original
function as derivative almost everywhere, including when it has jumps. -/
theorem integral_mul_of_moving_primitive {f w w' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) (hw : AbsolutelyContinuousOnInterval w a b)
    (hwd : ∀ x ∈ Set.Icc a b, HasDerivAt w (w' x) x) :
    (∫ x in a..b, w x * f x) =
      w b * (∫ t in a..b, f t) - ∫ x in a..b, w' x * (∫ t in a..x, f t) := by
  let P : ℝ → ℝ := fun x ↦ ∫ t in a..x, f t
  have hP : AbsolutelyContinuousOnInterval P a b :=
    hf.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hparts := hw.integral_mul_deriv_eq_deriv_mul hP
  have hleft : (∫ x in a..b, w x * deriv P x) = ∫ x in a..b, w x * f x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hmem
    have hxc : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hmem
    have hder := (hx hxc a Set.left_mem_uIcc).deriv
    change deriv P x = f x at hder
    rw [hder]
  have hright : (∫ x in a..b, deriv w x * P x) = ∫ x in a..b, w' x * P x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    change deriv w x * P x = w' x * P x
    rw [(hwd x hx).deriv]
  rw [hleft, hright] at hparts
  have hPa : P a = 0 := intervalIntegral.integral_same
  have hPb : P b = ∫ t in a..b, f t := rfl
  rw [hPa, hPb, mul_zero, sub_zero] at hparts
  exact hparts

end PseudoPrime.Analysis
