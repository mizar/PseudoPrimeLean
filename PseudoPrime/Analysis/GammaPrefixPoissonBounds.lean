/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorPrefixBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaAdaptivePoissonBounds

/-! # Eight-term per-node Poisson error certificate

Real digamma prefixes replace uniform Gamma corrections.
The signed resolvent retains its conductor coefficient with additive error below 199/10.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The certified rational Euler ratio plus the eight-term digamma allowance at the
 lower real Gamma argument of a resolvent node. This retains the exact node dependence
 and supplies the centered Poisson error. -/
noncomputable def gammaResolventPrefixEulerError (a : ℚ) : ℝ :=
  (((a : ℝ) - 1 / 2)⁻¹ ^ 2 + ((a : ℝ) + 1 / 2)⁻¹) /
      (1 + (gammaResolventDyadicLower a : ℝ) / ((a : ℝ) - 1 / 2)) +
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance ((1 / 2 + (a : ℝ)) / 2) 8

/-- The absolute weighted node-dependent errors sum to less than 199/10.
 Evaluate the signed coefficient list, dyadic denominators and eight-term rational prefixes.
 This is the improved additive zero-mass certificate. -/
theorem gammaResolvent_prefix_error_lt :
    (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * gammaResolventPrefixEulerError ab.1)).sum <
      (199 / 10 : ℝ) := by
  norm_num only [gammaResolventCoefficients, gammaResolventPrefixEulerError,
    gammaResolventDyadicLower, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance, Finset.sum_range_succ, Finset.sum_range_zero,
    max_def, ite_true, ite_false]

/-- Given the certified prefix errors for actual Poisson values, their signed resolvent
 combination is below M L+199/10. Preserve the signed conductor term and bound only the errors
 by absolute weights. This connects the finite certificate with the analytic sums. -/
theorem gammaResolvent_weighted_lt_of_prefix_bounds (P : ℚ → ℝ) (L : ℝ)
    (h :
      ∀ ab ∈ gammaResolventCoefficients, |P ab.1 - L / 2| ≤ gammaResolventPrefixEulerError ab.1) :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + 199 / 10 := by
  have ht :=
    sum_signed_centered_le gammaResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ gammaResolventPrefixEulerError ab.1) (L / 2) h
  have he :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ = ((gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right gammaResolvent_prefix_error_lt _)

end PseudoPrime.Analysis
