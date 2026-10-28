/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrefixZeroMass

/-! # Variable-length digamma prefix error certificates

Any certified prefix error sum transfers to the actual Gamma zero mass.
A sixteen-term kernel-checked certificate gives additive 99/5.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a natural prefix length m and rational resolvent scale a, the Euler-ratio allowance
 plus the real Gamma prefix allowance at the lower argument. This defines each node's error
 without fixing the prefix length. -/
noncomputable def gammaResolventEulerErrorWithPrefix (m : ℕ) (a : ℚ) : ℝ :=
  (((a : ℝ) - 1 / 2)⁻¹ ^ 2 + ((a : ℝ) + 1 / 2)⁻¹) /
      (1 + (gammaResolventDyadicLower a : ℝ) / ((a : ℝ) - 1 / 2)) +
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance ((1 / 2 + (a : ℝ)) / 2) m

/-- The sum of absolute resolvent weights times the m-term per-node errors.
 Its explicit finite expression is the only numerical input needed for the variable certificate.
 This permits longer prefixes without duplicating the analytic proof. -/
noncomputable def gammaResolventPrefixErrorSum (m : ℕ) : ℝ :=
  (gammaResolventCoefficients.map
      (fun ab ↦ |(ab.2 : ℝ)| * gammaResolventEulerErrorWithPrefix m ab.1)).sum

/-- The sixteen-term absolute weighted error sum is below 99/5.
 Evaluate the exact rational coefficients, reciprocal prefixes and maximum branches in the kernel.
 This supplies a concrete certificate for the variable zero-mass API. -/
theorem gammaResolvent_sixteen_error_lt : gammaResolventPrefixErrorSum 16 < (99 / 5 : ℝ) := by
  norm_num only [gammaResolventPrefixErrorSum, gammaResolventCoefficients,
    gammaResolventEulerErrorWithPrefix, gammaResolventDyadicLower,
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Finset.sum_range_succ, Finset.sum_range_zero, max_def, ite_true, ite_false]

/-- The thirty-two-term absolute weighted error is below 197/10.
 Evaluate the exact reciprocal prefixes and coefficient weights in the kernel.
 This extends the shared certificate API without another analytic mass proof. -/
theorem gammaResolvent_thirtyTwo_error_lt : gammaResolventPrefixErrorSum 32 < (197 / 10 : ℝ) := by
  norm_num only [gammaResolventPrefixErrorSum, gammaResolventCoefficients,
    gammaResolventEulerErrorWithPrefix, gammaResolventDyadicLower,
    AnalyticNumberTheory.Gamma.gammaPrefixAllowance, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Finset.sum_range_succ, Finset.sum_range_zero, max_def, ite_true, ite_false]

/-- Given an m-term numerical error certificate and the centered Poisson inequalities,
 the signed resolvent combination is below M L+C. Keep signs in the conductor term and
 use absolute weights only for the error.
 This connects any certified length with the Poisson sum. -/
theorem gammaResolvent_weighted_lt_of_variable_prefix (P : ℚ → ℝ) (L : ℝ) (m : ℕ) {C : ℝ}
    (hC : gammaResolventPrefixErrorSum m < C)
    (h :
      ∀ ab ∈ gammaResolventCoefficients,
        |P ab.1 - L / 2| ≤ gammaResolventEulerErrorWithPrefix m ab.1) :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + C := by
  have ht :=
    sum_signed_centered_le gammaResolventCoefficients (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ gammaResolventEulerErrorWithPrefix m ab.1) (L / 2) h
  have he :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum * (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ = ((gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2) * L := by ring
      _ = _ := by rw [gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right hC _)

end PseudoPrime.Analysis
