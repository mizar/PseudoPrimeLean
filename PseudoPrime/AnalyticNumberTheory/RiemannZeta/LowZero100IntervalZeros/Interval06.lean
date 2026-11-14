/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FirstZeros
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointInterface
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node06Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node06Upper

/-! # Critical-line zero in candidate interval 06 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Candidate interval 06, from `4811/128` to that value plus `1/100`,
contains a critical-line zeta zero. Internally verified endpoint margins give a sign change,
and continuity provides the zero without assuming RH. -/
theorem low_zero_06_exists :
    ∃ t ∈ Set.Ioo (4811 / 128 : ℝ) (4811 / 128 + 1 / 100),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have h :=
    exists_zero_of_endpoint_checks (4811 / 128) (by norm_num only) (by norm_num only)
      endpoint_06_lower_check.1 endpoint_06_upper_check.1
      (Or.inr ⟨endpoint_06_upper_check.2, endpoint_06_lower_check.2⟩)
  simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
