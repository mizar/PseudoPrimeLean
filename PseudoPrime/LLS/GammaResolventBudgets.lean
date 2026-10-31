/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.RationalResolventApproximation
public import PseudoPrime.Analysis.SignedFiniteErrorBounds
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Rational coefficients for the Gamma resolvent certificate

The finite arithmetic certifies scales, parity arguments, conductor weight, and
signed error allowance. Global domination of Gamma and individual Poisson errors
are separate analytic obligations.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The sum of absolute weights times the per-line logarithmic-derivative and
archimedean error allowance is less than 279. Evaluate the exact rational expression
in the reals. This bounds the signed-comparison error once the line estimates hold. -/
theorem gammaResolvent_error_lt :
    (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (((ab.1 : ℝ) - 1 / 2)⁻¹ ^ 2 + ((ab.1 : ℝ) - 1 / 2)⁻¹ + 6))).sum <
      (279 : ℝ) := by
  norm_num only [AnalyticNumberTheory.Gamma.gammaResolventCoefficients, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]

/-- If each supplied Poisson value has the displayed centered error bound, the
signed finite combination is less than the certified conductor coefficient times L plus 279.
Preserve signs in the common main term and use absolute weights only for the errors.
The individual Poisson estimates and global Gamma majorant are separate obligations. -/
theorem gammaResolvent_weighted_lt_of_centered_bounds (P : ℚ → ℝ) (L : ℝ)
    (h :
      ∀ ab ∈ AnalyticNumberTheory.Gamma.gammaResolventCoefficients,
        |P ab.1 - L / 2| ≤ ((ab.1 : ℝ) - 1 / 2)⁻¹ ^ 2 + ((ab.1 : ℝ) - 1 / 2)⁻¹ + 6) :
    (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * P ab.1)).sum <
      (11783423 / 25000000 : ℝ) * L + 279 := by
  have ht :=
    Analysis.sum_signed_centered_le AnalyticNumberTheory.Gamma.gammaResolventCoefficients
      (fun ab ↦ (ab.2 : ℝ)) (fun ab ↦ P ab.1)
      (fun ab ↦ ((ab.1 : ℝ) - 1 / 2)⁻¹ ^ 2 + ((ab.1 : ℝ) - 1 / 2)⁻¹ + 6) (L / 2) h
  have he :
    (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum *
        (L / 2) =
      (11783423 / 25000000 : ℝ) * L := by
    calc
      _ =
          ((AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum /
              2) *
            L :=
        by ring
      _ = _ := by rw [AnalyticNumberTheory.Gamma.gammaResolvent_mass_eq]
  rw [he] at ht
  exact ht.trans_lt (add_lt_add_right gammaResolvent_error_lt _)

end PseudoPrime.LLS
