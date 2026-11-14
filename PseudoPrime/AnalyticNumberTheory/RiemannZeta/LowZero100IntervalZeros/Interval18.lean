/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FirstZeros
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointInterface
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node18Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100EndpointChecks.Node18Upper

/-! # Critical-line zero in candidate interval 18 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Candidate interval 18, from `18449/256` to that value plus `1/100`,
contains a critical-line zeta zero. Internally verified endpoint margins give a sign change,
and continuity provides the zero without assuming RH. -/
theorem low_zero_18_exists :
    ∃ t ∈ Set.Ioo (18449 / 256 : ℝ) (18449 / 256 + 1 / 100),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have h :=
    exists_zero_of_endpoint_checks (18449 / 256) (by norm_num only) (by norm_num only)
      endpoint_18_lower_check.1 endpoint_18_upper_check.1
      (Or.inr ⟨endpoint_18_upper_check.2, endpoint_18_lower_check.2⟩)
  simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
