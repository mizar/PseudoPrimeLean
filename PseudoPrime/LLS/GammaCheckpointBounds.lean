/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerSeedBoundaryBounds
public import PseudoPrime.Analysis.GammaFiniteEulerBlockCombination

/-! # Euler-prefix half-line bounds from an arbitrary certified checkpoint -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH, a>=50000, a<=b and a rational upper bound U for the boundary tail at a.
Claim: the prefix at b is at least 61423/5000-U. Proof: transport the seed to a and
use nonnegative prefix monotonicity. Role: replace the fixed cutoff 89100 by any checkpoint. -/
theorem gamma_prefix_lower_of_checkpoint (hRH : RiemannHypothesis) {a b : ℝ} {U : ℚ}
    (ha : 50000 ≤ a) (hab : a ≤ b) (hU : gammaEulerBoundaryTail a ≤ (U : ℝ)) :
    ((61423 / 5000 - U : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hp := gamma_euler_prefix_lower_of_tail_upper hRH ha hU
  have hcast :
    ((61423 / 5000 - U : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    exact hp
  exact Analysis.gamma_euler_prefix_lower_mono (Nat.floor_mono hab) hcast

/-- Input: a checked boundary-tail checkpoint and a dual-budget upper bound D.
Claim: the factor-free joint budget has the displayed bound for every later cutoff b.
Proof: retain the transported prefix gain with coefficient negative two.
Role: provide a common-endpoint bound without checking boundary tails throughout a cell. -/
theorem gamma_joint_budget_le_of_checkpoint (hRH : RiemannHypothesis) {a b L x D : ℝ} {U : ℚ}
    (ha : 50000 ≤ a) (hab : a ≤ b) (hU : gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaFactorFreeJointBudget L b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * ((61423 / 5000 - U : ℚ) : ℝ) := by
  have hp := gamma_prefix_lower_of_checkpoint hRH ha hab hU
  unfold gammaFactorFreeJointBudget
  linarith only [hp, hD]

/-- Input: L, x, dual cap D and checkpoint tail cap U.
Definition: the factor-free margin with the prefix replaced by 61423/5000-U.
Output: a scalar lower margin. Role: isolate the remaining numerical separation obligation. -/
noncomputable def gammaCheckpointSeparation (L x D : ℝ) (U : ℚ) : ℝ :=
  2 *
      ((∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) * Real.sqrt x -
        gammaRampPairedErrorNumerator x / Real.sqrt x) -
    (Real.sqrt x +
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x) -
    ((11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * ((61423 / 5000 - U : ℚ) : ℝ) + 11 +
      ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x +
      43 * x ^ (-9 / 16 : ℝ))

/-- Input: RH, a valid boundary checkpoint and an actual dual upper cap.
Claim: the checkpoint margin bounds the actual factor-free separation below.
Proof: subtract the checkpoint joint-budget upper bound.
Role: connect arbitrary-checkpoint certificates to actual quadratic witnesses. -/
theorem gamma_checkpoint_separation_le (hRH : RiemannHypothesis) {a b L x D : ℝ} {U : ℚ}
    (ha : 50000 ≤ a) (hab : a ≤ b) (hU : gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaCheckpointSeparation L x D U ≤ gammaFactorFreeSeparation L b x := by
  have hj := gamma_joint_budget_le_of_checkpoint hRH ha hab hU hD
  unfold gammaCheckpointSeparation gammaFactorFreeSeparation
  linarith only [hj]

end PseudoPrime.LLS
