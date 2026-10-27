/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneDeciShiftSeparation

/-! # Exact entrance obstruction for the retained logarithm minorant -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- For an arbitrary conductor allowance c, evaluate the retained comparison
at root eight and its rational logarithm minorant. Expanding the definitions
gives the exact affine cost. This identifies the limit of this minorant. -/
theorem qNeOneShiftGap_at_eight (c : ℝ) :
    qNeOneRetainedGap 8 (qNeOneRetainedLogLower 8) -
        (c - 1 / 1000) *
          ((2 * 8 + 2 + 2 * qNeOneRetainedLogLower 8) * (8 ^ 2 - 1) / 2 +
            qNeOneRetainedLogLower 8 * (8 - 1) ^ 2) =
      244047829 / 3000000 - (99981 / 125 : ℝ) * c := by
  norm_num only [qNeOneRetainedGap, qNeOneRetainedLogLower]
  ring

/-- The affine endpoint gap is positive exactly below the stated rational
threshold. Rational linear arithmetic proves both directions.
This makes the endpoint restriction available without numerical approximations. -/
theorem qNeOneShiftGap_at_eight_pos_iff (c : ℝ) :
    0 < 244047829 / 3000000 - (99981 / 125 : ℝ) * c ↔ c < 244047829 / 2399544000 := by
  constructor
  · intro h
    linarith only [h]
  · intro h
    linarith only [h]

/-- For a conductor allowance at or above the threshold, the retained rational
minorant cannot certify a positive gap at root eight. Rewrite the exact endpoint
identity and use the positivity equivalence. This is a restriction on this
comparison method, rather than on actual least witnesses. -/
theorem qNeOneShiftGap_at_eight_not_pos {c : ℝ} (hc : (244047829 / 2399544000 : ℝ) ≤ c) :
    ¬0 <
        qNeOneRetainedGap 8 (qNeOneRetainedLogLower 8) -
          (c - 1 / 1000) *
            ((2 * 8 + 2 + 2 * qNeOneRetainedLogLower 8) * (8 ^ 2 - 1) / 2 +
              qNeOneRetainedLogLower 8 * (8 - 1) ^ 2) := by
  rw [qNeOneShiftGap_at_eight]
  exact fun h ↦ (not_lt_of_ge hc) ((qNeOneShiftGap_at_eight_pos_iff c).mp h)

end PseudoPrime.LLS.Extensions
