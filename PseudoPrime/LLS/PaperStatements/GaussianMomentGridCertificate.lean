/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGridIntegerCaps

/-! # Kernel-certified finite Gaussian moment bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The 256 rounded profile caps have the stated exact integer sum.
Kernel evaluation checks the fixed-point Taylor and ceiling computations. -/
theorem gaussian_grid_cap_sum_profile :
    (∑ i ∈ Finset.range 256, gaussianGridOuterCap i 1) = 781906691 := by decide +kernel

/-- The 256 rounded endpoint caps have the stated exact integer sum.
Kernel evaluation checks the fixed-point Taylor and ceiling computations. -/
theorem gaussian_grid_cap_sum_endpoint :
    (∑ i ∈ Finset.range 256, gaussianGridOuterCap i 3) = 561460149 := by decide +kernel

/-- The profile and cutoff-weighted endpoint integrals on [-4,4] satisfy
explicit rational upper bounds. Insert the kernel-certified integer sums into
the finite-grid integral comparison. The tails are handled separately. -/
theorem gaussian_grid_finite_moment_bounds :
    (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        (138056 / 1000000 : ℝ) ∧
      (21 / 10 : ℝ) * (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) ≤
        (208180 / 1000000 : ℝ) := by
  have h := gaussian_grid_256_integer_caps
  rw [gaussian_grid_cap_sum_profile, gaussian_grid_cap_sum_endpoint] at h
  constructor
  · norm_num only [Nat.cast_ofNat] at h ⊢
    linarith only [h.1]
  · norm_num only [Nat.cast_ofNat] at h ⊢
    linarith only [h.2]

end PseudoPrime.LLS.PaperStatements
