/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeChebyshevBounds
public import PseudoPrime.Analysis.RepeatedSqrt

/-! # Explicit three-quarter Chebyshev error under RH -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, the Chebyshev psi function has error at most `t^(3/4)` for
`t ≥ 625`, expressed using repeated square roots. A relative width of
`1 / (3 * t^(1/4))` gives the required explicit constants. -/
theorem psi_error_quarter_sqrt (hRH : RiemannHypothesis) {t : ℝ} (ht : 625 ≤ t) :
    |Chebyshev.psi t - t| ≤ Real.sqrt t * Real.sqrt (Real.sqrt t) := by
  let u : ℝ := Real.sqrt (Real.sqrt t)
  let h : ℝ := 1 / (3 * u)
  have ht0 : 0 ≤ t := by linarith only [ht]
  have hs0 := Real.sqrt_nonneg t
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hs : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0
  have hu : u ^ 2 = Real.sqrt t := Real.sq_sqrt hs0
  have hu5 : 5 ≤ u := by
    have h25 : (25 : ℝ) ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by nlinarith only [ht])
    dsimp only [u]
    exact Real.le_sqrt_of_sq_le (by nlinarith only [h25])
  have huPos : 0 < u := by linarith only [hu5]
  have htPow : t = u ^ 4 := by nlinarith only [hu, hs]
  have hh : 0 < h := by
    dsimp only [h]; positivity
  have hhHalf : h ≤ 1 / 2 := by
    dsimp only [h]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * u)).2
    nlinarith only [hu5]
  have hroot : Real.sqrt (1 + h) ≤ 1 + h / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hh]
    · nlinarith only [sq_nonneg h]
  have hrootT : Real.sqrt ((1 + h) * t) ≤ Real.sqrt t * (1 + h / 2) := by
    rw [Real.sqrt_mul (by linarith only [hh])]
    nlinarith only [mul_nonneg hs0 (sub_nonneg.mpr hroot)]
  have hp := psi_upper_relative_log_shift hRH hh (show (1 : ℝ) < t by linarith only [ht])
  have hm := psi_lower_relative_log_shift hRH hh hhHalf ht0
  have h2 : 5 * u ≤ u ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hu5) hu0]
  have h3 : 5 * u ^ 2 ≤ u ^ 3 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hu5) (sq_nonneg u)]
  have hconst : 125 ≤ u ^ 3 := by nlinarith only [hu5, h2, h3]
  have hupper :
    h * t +
        (Real.sqrt t / 20 + 21 / 20 + (Real.sqrt t * (1 + h / 2) / 20 + 21 / 20)) * (1 + h) / h ≤
      u ^ 3 := by
    rw [← hu, htPow]
    dsimp only [h]
    field_simp [ne_of_gt huPos]
    nlinarith only [hu5, h2, h3, hconst]
  have hlower : h * t + (Real.sqrt t / 10 + 21 / 10) / h + 1839 / 1000 ≤ u ^ 3 := by
    rw [← hu, htPow]
    dsimp only [h]
    field_simp [ne_of_gt huPos]
    nlinarith only [hu5, h2, h3, hconst]
  have hfactor : 0 ≤ (1 + h) / h := div_nonneg (by linarith only [hh]) hh.le
  have hrootComp := mul_le_mul_of_nonneg_right hrootT hfactor
  have hu3 : Real.sqrt t * u = u ^ 3 := by
    rw [← hu]; ring
  change |Chebyshev.psi t - t| ≤ Real.sqrt t * u
  rw [hu3]
  apply abs_le.mpr
  constructor
  · nlinarith only [hm, hlower, hu]
  · simp only [div_eq_mul_inv] at hp hupper hrootComp
    nlinarith only [hp, hupper, hrootComp]

end PseudoPrime.LLS
