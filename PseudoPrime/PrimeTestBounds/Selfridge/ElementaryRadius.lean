/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTestBounds.Selfridge.Comparison
import PseudoPrime.PrimeTestBounds.Selfridge.LogGRH

/-!
# GRH elementary radius application
-/

namespace PseudoPrime.PrimeTestBounds.Selfridge

/--
Under GRH, for odd nonsquare `n ≥ 3`, the absolute classical `≠1` stopping value is at most
the absolute pure `-1` stopping value, and the latter is at most
`(log(4n) + (24/5)*loglog(4n) + 3)²`.
The proof pairs the preceding absolute-value comparison with
`classicalSelfridgeD_firstStopNegOne_natAbs_cast_le_log_sq_of_3_le`, providing both pointwise
inequalities in one public theorem. Nonemptiness of the stopping sets is supplied internally.
-/
theorem classicalSelfridgeD_elementary_bound_explicit
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 := by
  have hleft := classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_firstStopNegOne_natAbs_cast hn hns
  have hright := classicalSelfridgeD_firstStopNegOne_natAbs_cast_le_log_sq_of_3_le hGRH hn3 hn hns
  exact ⟨hleft, hright⟩

end PseudoPrime.PrimeTestBounds.Selfridge
