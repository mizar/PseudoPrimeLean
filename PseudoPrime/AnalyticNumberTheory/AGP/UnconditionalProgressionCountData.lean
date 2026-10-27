/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.UnconditionalNarrowThetaSupply
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimorialProgressionCountData

/-! # Unconditional AGP progression count data -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/-- Construct the original AGP progression count data without analytic input assumptions.
Apply the unconditional narrow theta supply to the existing primorial seed and coarse sieve
bridge. This is the final analytic input to the finite-base Carmichael construction. -/
theorem agp_progression_count_data_exists_unconditional : AGPProgressionCountDataExists := by
  obtain ⟨J, D, Xtheta, hJ, hSupply⟩ := exists_unconditional_narrow_theta_supply
  exact agp_progression_count_data_exists_of_primorial_p2_and_theta_supply J D Xtheta hJ hSupply

end PseudoPrime.AnalyticNumberTheory.AGP
