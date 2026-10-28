/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorRefinedBounds

/-! # Adaptive centered Poisson bounds for the Gamma resolvent

Later nodes use the sharper Gamma correction 9/10.
The exact finite weighted Euler allowance is below 211/10.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational Euler allowance at scale a plus its archimedean correction.
 Nodes a≥3/2 use 9/10; earlier nodes retain 8/5. Certified dyadic denominators are unchanged.
 This defines the improved per-node centered error. -/
noncomputable def gammaResolventAdaptiveEulerError (a : ℚ) : ℝ :=
  (((a : ℝ) - 1 / 2)⁻¹ ^ 2 + ((a : ℝ) + 1 / 2)⁻¹) /
      (1 + (gammaResolventDyadicLower a : ℝ) / ((a : ℝ) - 1 / 2)) +
    (if (3 / 2 : ℝ) ≤ (a : ℝ) then 9 / 10 else 8 / 5)

/-- The absolute weighted adaptive errors sum to less than 211/10.
 Evaluate the exact rational expressions in the kernel. This is the new additive mass budget. -/
theorem gammaResolvent_adaptive_error_lt :
    (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * gammaResolventAdaptiveEulerError ab.1)).sum <
      (211 / 10 : ℝ) := by
  norm_num only [gammaResolventCoefficients, gammaResolventAdaptiveEulerError,
    gammaResolventDyadicLower, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ite_true,
    ite_false]

/-- Certified adaptive Poisson errors imply the signed resolvent bound with additive 211/10.
 Keep signs in the conductor coefficient and use absolute weights only for the errors.
 This connects the improved finite certificate to actual Poisson sums. -/
theorem gammaResolvent_weighted_lt_of_adaptive_bounds (P : ℚ → ℝ) (L : ℝ)
    (h :
      ∀ ab ∈ gammaResolventCoefficients, |P ab.1 - L / 2| ≤ gammaResolventAdaptiveEulerError ab.1) :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + 211 / 10 := by
  have ht :=
    sum_signed_centered_le gammaResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ gammaResolventAdaptiveEulerError ab.1) (L / 2) h
  have he :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ = ((gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right gammaResolvent_adaptive_error_lt _)

end PseudoPrime.Analysis
