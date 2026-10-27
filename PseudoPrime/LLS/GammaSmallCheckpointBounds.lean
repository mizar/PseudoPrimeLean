/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpointBounds
public import PseudoPrime.LLS.GammaEulerSeedBoundaryBounds

/-! # Euler prefix transport from small analytic checkpoints -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a checkpoint at least three, a later cutoff and a checkpoint error cap E.
Claim: the combined seed and target error is at most 3/40+E.
Proof: use error-budget antitonicity and the checked seed cap.
Role: transport a checkpoint error certificate to the entire later half-line. -/
theorem gamma_error_seed100_add_le_of_checkpoint {a b E : ℝ} (ha : 3 ≤ a) (hab : a ≤ b)
    (hE : gammaEulerTailErrorBudget a ≤ E) :
    gammaEulerTailErrorBudget 100 + gammaEulerTailErrorBudget b ≤ 3 / 40 + E := by
  have hm := gammaEulerTailErrorBudget_antitone_of_three_le ha hab
  linarith only [gammaEulerTailErrorBudget_le_seed100, hm, hE]

/-- Input: b >= 100. Claim: the combined seed and target error is at most 3/20.
Proof: specialize the general error transfer to the seed itself.
Role: avoid imposing the old target cutoff 50000. -/
theorem gamma_error_seed100_add_le_three_twentieths {b : ℝ} (hb : 100 ≤ b) :
    gammaEulerTailErrorBudget 100 + gammaEulerTailErrorBudget b ≤ (3 / 20 : ℝ) := by
  have h :=
    gamma_error_seed100_add_le_of_checkpoint (by norm_num only : (3 : ℝ) ≤ 100) hb
      gammaEulerTailErrorBudget_le_seed100
  linarith only [h]

/-- Input: RH, a checkpoint a >= 3, a later cutoff and rational boundary/error caps U,E.
Claim: the full prefix is at least 2457/200-E-U.
Proof: keep the two one-sided transport errors and use the checked seed boundary.
Role: retain a smaller checkpoint's certified error rather than a fixed uniform cap. -/
theorem gamma_prefix_lower_of_checkpoint_error (hRH : RiemannHypothesis) {a b : ℝ} {E U : ℚ}
    (ha : 3 ≤ a) (hab : a ≤ b) (hU : gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hE : gammaEulerTailErrorBudget a ≤ (E : ℝ)) :
    ((2457 / 200 - E - U : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hp :=
    gamma_euler_prefix_lower_from_seed100 hRH (show (1 : ℝ) ≤ a by linarith only [ha])
      (gamma_seed100_boundary_tail_lower hRH) hU
      (gamma_error_seed100_add_le_of_checkpoint ha (le_refl a) hE)
  have hc :
    ((2457 / 200 - E - U : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hp]
  exact Analysis.gamma_euler_prefix_lower_mono (Nat.floor_mono hab) hc

/-- Input: RH, 100 <= a <= b and a rational boundary-tail cap U at a.
Claim: the full prefix at b is at least 1221/100-U.
Proof: bound the two errors by 3/20, transport the seed and use prefix monotonicity.
Role: replace a >= 50000 by a >= 100 in checkpoint-based witness estimates. -/
theorem gamma_prefix_lower_of_small_checkpoint (hRH : RiemannHypothesis) {a b : ℝ} {U : ℚ}
    (ha : 100 ≤ a) (hab : a ≤ b) (hU : gammaEulerBoundaryTail a ≤ (U : ℝ)) :
    ((1221 / 100 - U : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hp :=
    gamma_euler_prefix_lower_from_seed100 hRH (show (1 : ℝ) ≤ a by linarith only [ha])
      (gamma_seed100_boundary_tail_lower hRH) hU (gamma_error_seed100_add_le_three_twentieths ha)
  have hc :
    ((1221 / 100 - U : ℚ) : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hp]
  exact Analysis.gamma_euler_prefix_lower_mono (Nat.floor_mono hab) hc

/-- Input: scale L,x, dual cap D and rational prefix lower bound C.
Definition: the existing checkpoint margin with its tail parameter replaced so the prefix is C.
Output: an explicit real scalar margin. Role: separate prefix estimates from checkpoint choice. -/
noncomputable def gammaPrefixSeparation (L x D : ℝ) (C : ℚ) : ℝ :=
  gammaCheckpointSeparation L x D (61423 / 5000 - C)

/-- Input: an actual prefix lower bound C and signed dual upper bound D.
Claim: the corresponding scalar margin bounds the actual separation below.
Proof: substitute the two bounds in the factor-free expression.
Role: connect arbitrary proved prefix estimates without an RH assumption on this algebraic step. -/
theorem gamma_prefix_separation_le_of_prefix {b L x D : ℝ} {C : ℚ}
    (hC : (C : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaPrefixSeparation L x D C ≤ gammaFactorFreeSeparation L b x := by
  unfold gammaPrefixSeparation gammaCheckpointSeparation gammaFactorFreeSeparation
    gammaFactorFreeJointBudget
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
  linarith only [hC, hD]

/-- Input: RH, 100 <= a <= b, a boundary cap at a and an actual dual cap.
Claim: the small-checkpoint margin bounds the actual separation below.
Proof: combine the proved prefix transport with the algebraic margin transfer.
Role: remove the target error-budget assumption from the small-checkpoint witness interface. -/
theorem gamma_small_checkpoint_separation_le (hRH : RiemannHypothesis) {a b L x D : ℝ} {U : ℚ}
    (ha : 100 ≤ a) (hab : a ≤ b) (hU : gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaPrefixSeparation L x D (1221 / 100 - U) ≤ gammaFactorFreeSeparation L b x := by
  exact
    gamma_prefix_separation_le_of_prefix (gamma_prefix_lower_of_small_checkpoint hRH ha hab hU) hD

end PseudoPrime.LLS
