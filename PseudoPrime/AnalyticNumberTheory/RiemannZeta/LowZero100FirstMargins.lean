/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalNormalizedSign
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FastBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node01Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node01Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node02Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node02Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node03Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node03Upper

/-! # Margins for the first three low-zero intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

set_option maxHeartbeats 4000000 in
-- The conjunction instantiates six exact endpoint certificates.
/-- The six endpoints of the first three candidate intervals have the prescribed alternating
normalized zeta margins of `9/100000`. The result is unconditional and uses only internally
checked rational approximations and their proved analytic error bounds. -/
theorem low_zero_first_three_margins :
    RiemannXi.normalizedZeta ((14473 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((14473 / 1024 : ℚ) + 1 / 100) : ℝ) ∧
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta ((10763 / 512 : ℚ) : ℝ) ∧
      RiemannXi.normalizedZeta (((10763 / 512 : ℚ) + 1 / 100) : ℝ) < -(9 / 100000 : ℝ) ∧
      RiemannXi.normalizedZeta ((25611 / 1024 : ℚ) : ℝ) < -(9 / 100000 : ℝ) ∧
      (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (((25611 / 1024 : ℚ) + 1 / 100) : ℝ) := by
  exact
    ⟨endpoint_fast_negative_margin (14473 / 1024) (by norm_num only) (by norm_num only)
        endpoint_01_lower_check.1 endpoint_01_lower_check.2,
      (by
        simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
          (endpoint_fast_positive_margin ((14473 / 1024 : ℚ) + 1 / 100) (by norm_num only)
            (by norm_num only) endpoint_01_upper_check.1 endpoint_01_upper_check.2)),
      endpoint_fast_positive_margin (10763 / 512) (by norm_num only) (by norm_num only)
        endpoint_02_lower_check.1 endpoint_02_lower_check.2,
      (by
        simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
          (endpoint_fast_negative_margin ((10763 / 512 : ℚ) + 1 / 100) (by norm_num only)
            (by norm_num only) endpoint_02_upper_check.1 endpoint_02_upper_check.2)),
      endpoint_fast_negative_margin (25611 / 1024) (by norm_num only) (by norm_num only)
        endpoint_03_lower_check.1 endpoint_03_lower_check.2,
      (by
        simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
          (endpoint_fast_positive_margin ((25611 / 1024 : ℚ) + 1 / 100) (by norm_num only)
            (by norm_num only) endpoint_03_upper_check.1 endpoint_03_upper_check.2))⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
