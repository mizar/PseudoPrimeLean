/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPolePrincipalVariation

/-! # Principal finite sum at the unit cutoff -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- The scaled weight on the positive unit cutoff is bounded by `10/sqrt x`. -/
theorem fourScaledWeight_abs_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (htx : t ≤ x) :
    |fourScaledWeight x t| ≤ 10 / Real.sqrt x := by
  have hu := div_pos ht hx
  have hl : Real.log (t / x) ≤ 28 / 25 :=
    (Real.log_nonpos hu.le ((div_le_one hx).mpr htx)).trans (by norm_num only)
  have hb := fourPoleKernelWeight_bounds hu hl
  dsimp only [fourScaledWeight]
  rw [abs_div, abs_of_nonneg hb.1, abs_of_nonneg (Real.sqrt_nonneg x)]
  exact div_le_div_of_nonneg_right hb.2 (Real.sqrt_nonneg x)

/-- For positive scale, the actual scaled weight is integrable from zero to the scale.
Continuity away from zero and a uniform bound avoid a zero-endpoint differentiability assumption. -/
theorem fourScaledWeight_integrable {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fourScaledWeight x) MeasureTheory.volume 0 x := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mpr
  have hc : ContinuousOn (fourScaledWeight x) (Set.Ioc 0 x) := fun t ht ↦
    (fourScaledWeight_hasDerivAt hx ht.1 ht.2).continuousAt.continuousWithinAt
  apply
    MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (hc.aestronglyMeasurable measurableSet_Ioc) (10 / Real.sqrt x)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs]
  exact fourScaledWeight_abs_le hx ht.1 ht.2

/-- For scales at least two, the omitted integral below two is at most `20/sqrt x`. -/
theorem fourScaledWeight_low_integral {x : ℝ} (hx : 2 ≤ x) :
    |∫ t : ℝ in (0 : ℝ)..2, fourScaledWeight x t| ≤ 20 / Real.sqrt x := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have h :=
    intervalIntegral.norm_integral_le_of_norm_le (by norm_num only : (0 : ℝ) ≤ 2) (μ :=
      MeasureTheory.volume) (f := fourScaledWeight x) (g := fun _ ↦ 10 / Real.sqrt x)
      (Filter.Eventually.of_forall
        (fun t ht ↦ by
          rw [Real.norm_eq_abs]
          exact fourScaledWeight_abs_le hx0 ht.1 (ht.2.trans hx)))
      intervalIntegrable_const
  rw [Real.norm_eq_abs, intervalIntegral.integral_const] at h
  norm_num only [sub_zero, smul_eq_mul] at h
  convert h using 1
  ring

/-- The full unit-cutoff integral is the square root of the scale
times the exact fourth-pole moment. -/
theorem fourScaledWeight_cutoff_integral {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in (0 : ℝ)..x, fourScaledWeight x t) =
      Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) := by
  dsimp only [fourScaledWeight]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div fourPoleKernelWeight hx.ne',
    zero_div, div_self hx.ne']
  have hcut :
    (∫ u : ℝ in (0 : ℝ)..1, fourPoleKernelWeight u) =
      (484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13)) :=
    rationalPole_four_cutoff
  rw [hcut]
  simp only [smul_eq_mul]
  have hs := Real.sq_sqrt hx.le
  have hn := (Real.sqrt_pos.mpr hx).ne'
  apply (div_eq_iff hn).mpr
  calc
    _ = Real.sqrt x ^ 2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) := by rw [hs]
    _ = _ := by ring

/-- Under RH and for scales at least two, the actual finite principal sum differs from
its exact unit-cutoff main term by at most `26 x^(1/4) + 40/sqrt x`.
Abel summation on `[2,x]` is combined with the explicit low-interval correction. -/
theorem fourPole_cutoff_principal_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13)))| ≤
      26 * x ^ (1 / 4 : ℝ) + 40 / Real.sqrt x := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have h0 := fourScaledWeight_integrable hx0
  have h02 : IntervalIntegrable (fourScaledWeight x) MeasureTheory.volume 0 2 :=
    h0.mono_set
      (by
        rw [Set.uIcc_of_le hx0.le, Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 2)]
        exact Set.Icc_subset_Icc_right hx)
  have h2 : IntervalIntegrable (fourScaledWeight x) MeasureTheory.volume 2 x :=
    h0.mono_set
      (by
        rw [Set.uIcc_of_le hx0.le, Set.uIcc_of_le hx]
        exact Set.Icc_subset_Icc_left (by norm_num only))
  have he := intervalIntegral.integral_add_adjacent_intervals h02 h2
  rw [fourScaledWeight_cutoff_integral hx0] at he
  have ht :=
    abs_sub
      ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∫ t : ℝ in (2 : ℝ)..x, fourScaledWeight x t))
      (∫ t : ℝ in (0 : ℝ)..2, fourScaledWeight x t)
  have hsum :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∫ t : ℝ in (2 : ℝ)..x, fourScaledWeight x t) -
        (∫ t : ℝ in (0 : ℝ)..2, fourScaledWeight x t) =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) := by
    linarith only [he]
  rw [hsum] at ht
  have ha := fourScaledWeight_error_le hRH hx
  have hb := fourScaledWeight_low_integral hx
  calc
    _ ≤ (26 * x ^ (1 / 4 : ℝ) + 20 / Real.sqrt x) + 20 / Real.sqrt x := ht.trans (add_le_add ha hb)
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements
