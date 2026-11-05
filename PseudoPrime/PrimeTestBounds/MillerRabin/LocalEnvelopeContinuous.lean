/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEnvelopeMonotone

/-! # Continuity of the common local witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive radius clamped at scale seven is continuous. The clamped
argument is positive and the finer radius is at least seven, so the logarithm
and both rational denominators are continuous throughout the real line. This
supplies continuity for the local envelope. -/
theorem local_adaptive_clamped_continuous :
    Continuous (fun s : ℝ ↦ Analysis.adaptivePart2CutoffRoot (max 7 s)) := by
  have hc : Continuous (fun s : ℝ ↦ max 7 s) := continuous_const.max continuous_id
  have hlog : Continuous (fun s : ℝ ↦ Real.log (max 7 s)) :=
    hc.log (fun s ↦ ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 7) (le_max_left _ _)))
  have hf : Continuous (fun s : ℝ ↦ Analysis.finerPart2CutoffRoot (max 7 s)) := by
    dsimp only [Analysis.finerPart2CutoffRoot]
    exact (hc.sub (continuous_const.mul hlog)).add continuous_const
  have hpos (s : ℝ) : 7 ≤ Analysis.finerPart2CutoffRoot (max 7 s) :=
    le_trans (by norm_num only)
      (Analysis.finerPart2Root_ge_36_5_of_639_100_le (by linarith only [le_max_left (7 : ℝ) s]))
  have hden (s : ℝ) : Analysis.finerPart2CutoffRoot (max 7 s) - 1 ≠ 0 :=
    ne_of_gt (by linarith only [hpos s])
  have hsq (s : ℝ) : Analysis.finerPart2CutoffRoot (max 7 s) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (by linarith only [hpos s]))
  dsimp only [Analysis.adaptivePart2CutoffRoot, Analysis.reciprocalLossBridge]
  exact
    (hf.sub continuous_const).add
      (continuous_const.mul
        ((continuous_const.add (continuous_const.div (hf.sub continuous_const) hden)).sub
          (continuous_const.div (hf.pow 2) hsq)))

/-- The common local envelope is continuous on the real line. Its weight,
clamped adaptive radius, squared terms and finite even envelope are continuous,
and finite minima and maxima preserve continuity. This is the continuity part
of the local contract used for the factor-type coverage. -/
theorem localFullEnvelope_continuous : Continuous localFullEnvelope := by
  have htheta : Continuous localInterpolationWeight :=
    continuous_const.min (continuous_const.max (continuous_id.sub continuous_const))
  have hguard : Continuous localInterpolatedGuard :=
    continuous_const.max
      (((continuous_const.sub htheta).mul (continuous_const.mul (continuous_id.pow 2))).add
        (htheta.mul (local_adaptive_clamped_continuous.pow 2)))
  exact
    ((continuous_id.pow 2).min ((local_adaptive_clamped_continuous.pow 2).min hguard)).min
      localEvenEnvelope_continuous

end PseudoPrime.PrimeTestBounds.MillerRabin
