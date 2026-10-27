/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpointBounds
public import PseudoPrime.LLS.GammaEulerBoundaryCells

/-! # A seed-only Euler-prefix lower bound from cutoff 50000 onward -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH. Claim: the signed Euler boundary tail at 50000 is at most 33/5.
Proof: retain the negative psi and smoothed-sum products using existing node bounds.
Role: certify a lower checkpoint without introducing new finite arithmetic payloads. -/
theorem gamma_boundary50000_upper (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 50000 ≤ (33 / 5 : ℝ) := by
  have ha :=
    gamma_target_boundary_arithmetic_lower hRH (le_refl (50000 : ℝ))
      (by norm_num only : (50000 : ℝ) ≤ 300000)
  norm_num only at ha
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 6716 / 1000000000)
      gamma_center_cutoff_weight_lower (by norm_num only : (0 : ℝ) ≤ 45410) ha.1
      gamma_center_cutoff_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 49945) ha.2
      gamma_center_cutoff_main_upper
  linarith only [h]

/-- Input: RH and b>=50000. Claim: the full Euler prefix is at least 28423/5000.
Proof: transport the seed to the checkpoint and use nonnegative prefix monotonicity.
Role: replace the old prefix entrance 89100 when analysing smaller witness scales. -/
theorem gamma_prefix50000_lower_halfline (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (28423 / 5000 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have hp :=
    gamma_prefix_lower_of_checkpoint (U := 33 / 5) hRH (le_refl (50000 : ℝ)) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_boundary50000_upper hRH)
  norm_num only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at hp
  linarith only [hp]

/-- Input: RH, b>=50000 and a signed dual cap D.
Claim: the checkpoint margin with tail cap 33/5 bounds the actual separation below.
Proof: apply the generic checkpoint transfer. Role: feed witness extraction below log scale 300. -/
theorem gamma_checkpoint50000_separation_le (hRH : RiemannHypothesis) {b L x D : ℝ} (hb : 50000 ≤ b)
    (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaCheckpointSeparation L x D (33 / 5) ≤ gammaFactorFreeSeparation L b x := by
  exact
    gamma_checkpoint_separation_le hRH (le_refl (50000 : ℝ)) hb
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_boundary50000_upper hRH)
      hD

end PseudoPrime.LLS
