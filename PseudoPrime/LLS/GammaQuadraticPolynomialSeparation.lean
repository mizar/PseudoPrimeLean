/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPairedPolynomialSeparation
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds

/-! # Shared polynomial criteria for quadratic witness comparisons -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: logarithmic level L, scale x and retained credit C. Definition:
existence of root and logarithm upper bounds with a nonnegative root coefficient
and positive paired scalar polynomial. Role: share the numerical condition
between general character and quadratic witness comparisons. -/
def GammaPairedPolynomialCondition (L x C : ℝ) : Prop :=
  ∃ R u : ℝ,
    Real.sqrt x ≤ R ∧
      Real.log ((101 / 40 : ℝ) * x) ≤ u ∧
      0 ≤ (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600 ∧
      0 <
        ((83125234337 / 100000000000 : ℝ) - 231 / 24700) * x -
          ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600) * R -
          (38017647 / 988000 : ℝ) * u -
          (7 / 6 : ℝ) * L -
          14082763 / 197600

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: an actual character-budget cap, a pole logarithm cap and positive
paired polynomial data at x >= 1. Claim: the common-cost margin is strictly
positive. Compare the pole and character budgets to the generic paired gap.
Role: transfer arbitrary local-cost improvements without recomputing a cell. -/
theorem gamma_joint_prefix_common_margin_pos_of_polynomial {q Q : ℕ} (χ : DirichletCharacter ℂ q)
    {L x b C R u : ℝ} (hx : 1 ≤ x) (hroot : Real.sqrt x ≤ R)
    (hlog : Real.log ((101 / 40 : ℝ) * x) ≤ u) (hlogQ : Real.log Q ≤ L)
    (hJ : gammaJointPrefixLocalBudget χ b x ≤ (11783423 / 25000000 : ℝ) * L - 2 * C)
    (hcoef : 0 ≤ (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600)
    (hpoly :
      0 <
        ((83125234337 / 100000000000 : ℝ) - 231 / 24700) * x -
          ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600) * R -
          (38017647 / 988000 : ℝ) * u -
          (7 / 6 : ℝ) * L -
          14082763 / 197600) :
    0 <
      gammaJointPrefixSeparationWithCommonCap Q χ b x (541 / 50)
        (gammaSignedVariationPrincipalCap x) := by
  have hs := Real.sqrt_nonneg x
  have hpole :=
    div_le_div_of_nonneg_right
      (show (7 / 6 : ℝ) * Real.log Q + 4 ≤ (7 / 6 : ℝ) * L + 4 by linarith only [hlogQ]) hs
  have hscalar := gamma_paired_scalar_lt_gap hx hroot hlog hcoef hpoly
  dsimp only [gammaJointPrefixSeparationWithCommonCap]
  linarith only [hJ, hpole, hscalar]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: scale x >= 1, an effective prefix credit after local and dyadic
costs, a signed dual cap and the shared polynomial condition at L+7/5.
Claim: the retained factor-free margin exceeds 7/60. Use the generic paired
comparison and retain twice the prefix gain. Role: supply every existing
quadratic witness and finite-maximum interface without new finite tables. -/
theorem gamma_retained_margin_gt_of_polynomial {L x b C D : ℝ} (hx : 1 ≤ x)
    (hcredit :
      C + (3 / 4 + D + 7 / 60) / 2 ≤
        ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hdual : gammaScaleSignedDualBudget L x ≤ D)
    (hpoly : GammaPairedPolynomialCondition (L + 7 / 5) x C) :
    7 / 60 < gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50 := by
  obtain ⟨R, u, hroot, hlog, hcoef, hp⟩ := hpoly
  have hs := gamma_paired_scalar_lt_gap hx hroot hlog hcoef hp
  dsimp only [gammaSignedPrincipalFactorFreeSeparation, gammaFactorFreeJointBudget]
  linarith only [hs, hcredit, hdual]

end PseudoPrime.LLS
