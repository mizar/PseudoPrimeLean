/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq
import PseudoPrime.SelfridgeBoundGrh.MaximumBridge

/-!
# Logarithmic bounds for aggregate Selfridge maxima

This module connects the already established aggregate scan equalities to the uniform
`PseudoPrime.PseudoSquare.QNeOne` logarithmic bound without introducing an import cycle between
the two layers.
-/

namespace PseudoPrime.SelfridgeBoundGrh

/--
Under GRH and `B ≥ 751`, the classical factor-detecting stopping-value maximum over
admissible inputs up to `B` is at most `(log B)²` as a real number.
Rewrite the maximum as `QNeOne B` using `classicalNeOneMaximum_eq_QNeOne_of_751_le`, then apply
`PseudoPrime.PseudoSquare.QNeOne_le_log_sq_of_grh` to obtain the aggregate bound.
-/
theorem classicalNeOneMaximum_cast_le_log_sq_of_751_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ} (hB : 751 ≤ B) :
    (classicalNeOneMaximum B : ℝ) ≤ (Real.log (B : ℝ)) ^ 2 := by
  rw [classicalNeOneMaximum_eq_QNeOne_of_751_le hB]
  exact PseudoSquare.QNeOne_le_log_sq_of_grh hGRH (by omega)

/--
Under GRH and `B ≥ 751`, the Wheel30 factor-detecting stopping-value maximum over
admissible inputs up to `B` is at most `(log B)²` as a real number.
Rewrite the maximum as `QNeOne B` using `wheel30NeOneMaximum_eq_QNeOne_of_751_le`, then apply
`PseudoPrime.PseudoSquare.QNeOne_le_log_sq_of_grh` to obtain the aggregate bound.
-/
theorem wheel30NeOneMaximum_cast_le_log_sq_of_751_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ} (hB : 751 ≤ B) :
    (wheel30NeOneMaximum B : ℝ) ≤ (Real.log (B : ℝ)) ^ 2 := by
  rw [wheel30NeOneMaximum_eq_QNeOne_of_751_le hB]
  exact PseudoSquare.QNeOne_le_log_sq_of_grh hGRH (by omega)

end PseudoPrime.SelfridgeBoundGrh
