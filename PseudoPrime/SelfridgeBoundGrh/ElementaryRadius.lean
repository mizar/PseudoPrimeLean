/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal
import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum
import PseudoPrime.PrimeTest.Selfridge.WitnessBounds

import PseudoPrime.PrimeTest.Selfridge.Coincidence
import PseudoPrime.PrimeTest.Selfridge.Nonempty
import PseudoPrime.SelfridgeBoundGrh.LogSq

/-! # Pointwise elementary-radius bounds for the classical Selfridge scan -/

namespace PseudoPrime.SelfridgeBoundGrh

/--
For odd nonsquare `n`, the absolute classical factor-detecting stopping value is at most
the absolute pure `-1` stopping value, both cast to the reals.
Nonemptiness of both stopping sets is supplied internally from oddness and nonsquareness;
it is not an additional hypothesis. The proof derives `1 < n`, applies the same-candidate
stopping comparison, and rewrites `selfridgeD_natAbs`. This supplies the first inequality
of `classicalSelfridgeD_elementary_bound_explicit`.
-/
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_firstStopNegOne_natAbs_cast {n : ℕ}
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) := by
  let hne := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  let hneg := PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns
  have hn1 : 1 < n := by
    have hneq : n ≠ 1 := by
      intro h
      subst n
      exact hns ⟨1, by norm_num only⟩
    have hnpos : 0 < n := by
      rcases hn with ⟨k, hk⟩
      omega
    omega
  have hle :
    PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n hne ≤
      PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hneg :=
    PrimeTest.firstStopNeOne_le_firstStopNegOne_same_candidates hn1 hneg
  simpa only [PrimeTest.selfridgeD_natAbs] using
    (show
      (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n hne : ℝ) ≤
        (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hneg : ℝ)
      by exact_mod_cast hle)

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

end PseudoPrime.SelfridgeBoundGrh
