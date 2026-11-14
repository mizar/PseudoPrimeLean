/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FirstZeros
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FourthMargin
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FastBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node04Upper

/-! # Critical-line zero in candidate interval 04 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Candidate interval 04, from `31155/1024` to that value plus `1/100`,
contains a critical-line zeta zero. Internally verified endpoint margins give a sign change,
and continuity provides the zero without assuming RH. -/
theorem low_zero_04_exists :
    ∃ t ∈ Set.Ioo (31155 / 1024 : ℝ) (31155 / 1024 + 1 / 100),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  apply exists_zero_of_normalized_signs (by norm_num only) (by norm_num only)
  right
  have hl := low_zero_fourth_lower_margin
  have hu :=
    endpoint_fast_negative_margin ((31155 / 1024 : ℚ) + 1 / 100) (by norm_num only)
      (by norm_num only) endpoint_04_upper_check.1 endpoint_04_upper_check.2
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hu
  constructor <;> linarith only [hl, hu]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
