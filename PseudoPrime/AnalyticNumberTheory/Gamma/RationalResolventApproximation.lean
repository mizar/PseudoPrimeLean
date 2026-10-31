/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-! # Rational resolvent approximation for the Gamma kernel -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- Ten rational pairs (a,b) defining the signed Gamma resolvent approximation.
The scale a determines a Poisson line Re s = 1/2+a; b is its signed weight.
Zero weights are retained to agree with the polynomial certificate's denominators.
Each a exceeds 1/2, as certified below. -/
def gammaResolventCoefficients : List (ℚ × ℚ) :=
  [(11 / 20, 56157519 / 100000000), (13 / 20, 0), (16 / 20, 16846179 / 100000000),
    (20 / 20, 52329992 / 100000000), (26 / 20, 0), (34 / 20, 144548748 / 100000000),
    (46 / 20, -206770197 / 100000000), (64 / 20, -10561870 / 100000000),
    (90 / 20, 50028438 / 100000000), (140 / 20, -8311425 / 100000000)]

/-- Every resolvent scale lies strictly to the right of one half. Direct rational
verification ensures the corresponding ordinary L-series point has real part greater than one.
-/
theorem gammaResolvent_scales_gt_half :
    gammaResolventCoefficients.Forall (fun ab ↦ (1 / 2 : ℚ) < ab.1) := by decide +kernel

/-- Both parity shifts of every resolvent node give real Gamma arguments in [1/2,17/4].
Verify all rational endpoints. The uniform digamma correction bound applies throughout this
interval. -/
theorem gammaResolvent_gamma_arguments :
    gammaResolventCoefficients.Forall
      (fun ab ↦
        ((1 / 2 : ℚ) ≤ (1 / 2 + ab.1) / 2 ∧ (1 / 2 + ab.1) / 2 ≤ 17 / 4) ∧
          ((1 / 2 : ℚ) ≤ (3 / 2 + ab.1) / 2 ∧ (3 / 2 + ab.1) / 2 ≤ 17 / 4)) := by
  decide +kernel

/-- Signed rational resolvent evaluated at real ordinate t. This defines the candidate
majorant as the finite sum b a/(a²+t²); global domination of Gamma is proved separately.
It is later summed against nonnegative zero multiplicities. -/
noncomputable def gammaResolventMajorant (t : ℝ) : ℝ :=
  (gammaResolventCoefficients.map
      (fun ab ↦ (ab.2 : ℝ) * ((ab.1 : ℝ) / ((ab.1 : ℝ) ^ 2 + t ^ 2)))).sum

/-- Half the total signed weight equals 11783423/25000000. Evaluate the rational
list after casting to the reals. This is the coefficient of the conductor logarithm
when the centered Poisson identities are combined. -/
theorem gammaResolvent_mass_eq :
    (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2 = (11783423 / 25000000 : ℝ) := by
  norm_num only [gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]

end PseudoPrime.AnalyticNumberTheory.Gamma
