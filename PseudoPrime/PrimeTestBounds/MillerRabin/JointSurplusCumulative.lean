/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneCumulativeA

/-! # Global surplus cumulative upper bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The global comparison function is nonnegative on every real scale. -/
theorem jointSurplusGlobal_nonneg (L : ℝ) : 0 ≤ jointSurplusGlobal L := by
  unfold jointSurplusGlobal jointSurplusCutoff
  exact
    le_min (mul_nonneg (by norm_num only) (sq_nonneg _))
      (le_min (mul_nonneg (by norm_num only) (sq_nonneg _))
        (mul_nonneg (by norm_num only) (sq_nonneg _)))

/-- Under GRH, monotonicity transfers the global bound to a common upper scale. -/
theorem jointSurplus_least_scale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ jointSurplusGlobal L := by
  exact
    (jointSurplus_least_bound hn ho hc hGRH).trans
      (jointSurplusGlobal_mono (Real.log_natCast_nonneg n) hlog)

/-- Intersect the previous cumulative bound with the global surplus function. -/
noncomputable def jointCumulative (N : ℕ) : ℝ :=
  min (smoothCumulative N) (jointSurplusGlobal (Real.log N))

/-- Under GRH, the joint cumulative envelope bounds every natural endpoint. -/
theorem cumulativeLeastPrime_le_joint (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (N : ℕ) : (cumulativeLeastPrime N : ℝ) ≤ jointCumulative N := by
  apply le_min (cumulativeLeastPrime_le_smooth hGRH N)
  have h :=
    cumulativeLeastPrime_le_base jointSurplusGlobal jointSurplusGlobal_nonneg
      (fun hn ho hc L hlog ↦ jointSurplus_least_scale hGRH hn ho hc L hlog) [] hGRH N
  simpa only [baseHistory] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
