/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLowNumerics
public import PseudoPrime.LLS.PaperStatements.EndpointLowPrime

/-! # Pointwise gap at the prime-rounding radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational radius just below `sqrt 479` used for the rounded witness. -/
noncomputable def lowRoundRadius : ℝ :=
  1094303 / 50000

/-- The maximal pair-logarithm level after the certified `600000` spacing
correction at the upper end of the low bridge. -/
noncomputable def lowRoundLevel : ℝ :=
  (2 / 3) * (9977 / 250) - (1 / 3) * (3217 / 625000)

set_option maxRecDepth 8192 in
/-- The logarithm of the fixed rounding radius is bounded below by a rational
Taylor certificate. The lower endpoint is used in the pointwise gap check. -/
theorem lowRound_log_lower : (30858498 / 10000000 : ℝ) ≤ Real.log lowRoundRadius := by
  have hc :
    Analysis.rationalLogIntervalCheck (1094303 / 50000) 5 16 (30858498 / 10000000)
        (30858501 / 10000000) =
      true := by
    decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  convert hl using 1 <;> norm_num only [lowRoundRadius]

/-- The pointwise gap is strictly positive at the rounded radius and every
level below the certified maximal pair logarithm. A rational gap anchor and
the nonnegative quadratic coefficients transfer the logarithm lower bound. -/
theorem lowRound_pointwise_gap {L : ℝ} (hL : L ≤ lowRoundLevel) :
    0 <
      LLS.PaperStatements.endpointPointwiseGap L (2096 / 1831) lowRoundRadius
        (Real.log lowRoundRadius) := by
  apply
    LLS.PaperStatements.pointwise_gap_from_quad (z₀ := 30858498 / 10000000) (a :=
      LLS.PaperStatements.lowPrimeA lowRoundRadius) (b :=
      LLS.PaperStatements.lowPrimeB lowRoundLevel lowRoundRadius) hL
      (by norm_num only [lowRoundRadius]) (by norm_num only) lowRound_log_lower
      (by norm_num only [LLS.PaperStatements.lowPrimeA, lowRoundRadius])
      (by
        norm_num only [LLS.PaperStatements.lowPrimeB, LLS.PaperStatements.lowPrimeV, lowRoundRadius,
          lowRoundLevel])
  · intro z
    rw [LLS.PaperStatements.lowPrime_gap_quad
        (by norm_num only [lowRoundRadius] : lowRoundRadius ≠ 0),
      LLS.PaperStatements.lowPrime_gap_quad
        (by norm_num only [lowRoundRadius] : lowRoundRadius ≠ 0)]
    ring
  · norm_num only [LLS.PaperStatements.endpointPointwiseGap,
      LLS.PaperStatements.fullEndpointEvenExactComparisonGap, Analysis.pointwiseReciprocalLoss,
      lowRoundLevel, lowRoundRadius]

end PseudoPrime.PrimeTestBounds.MillerRabin
