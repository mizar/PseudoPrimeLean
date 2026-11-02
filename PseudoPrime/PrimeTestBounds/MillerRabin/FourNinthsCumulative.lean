/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTightCumulativeBounds

/-! # Four-ninths common-scale cumulative witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the history-safe tightened Gaussian base with four ninths of the square of
the common logarithmic scale. This preserves the existing history guarantees. -/
noncomputable def fourNinthsHistoryBase (L : ℝ) : ℝ :=
  min (gaussianTightHistoryBase L) ((4 / 9 : ℝ) * L ^ 2)

/-- The common-scale base is nonnegative, including outside the target domain. -/
theorem fourNinthsHistoryBase_nonneg (L : ℝ) : 0 ≤ fourNinthsHistoryBase L := by
  exact le_min (gaussianTightHistoryBase_nonneg L) (mul_nonneg (by norm_num only) (sq_nonneg L))

/-- Under GRH the common-scale base bounds each least rejecting prime whose
logarithm is at most the scale. The global witness and monotonicity of the
squared logarithm supply the new branch of the minimum. -/
theorem leastPrime_le_fourNinthsScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ fourNinthsHistoryBase L := by
  apply le_min (leastPrime_le_gaussianTightBase hGRH hn ho hc L hlog)
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_witness_four_ninths hn ho hc hGRH
  have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
  have h0 := Real.log_natCast_nonneg n
  have hs := (sq_le_sq₀ h0 (h0.trans hlog)).mpr hlog
  exact
    ((Nat.cast_le.mpr hm).trans hb).trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 4 / 9))

/-- Propagate the four-ninths common-scale base through the certified profile
history. Earlier inputs remain covered when a later profile becomes active. -/
noncomputable def fourNinthsCumulativeEnvelope (N : ℕ) : ℝ :=
  baseHistory TriangularProfile.T TriangularProfile.C fourNinthsHistoryBase historyProfiles
    (Real.log N)

/-- Under GRH the cumulative maximum of least rejecting primes through `N` is
bounded by the four-ninths history envelope, including empty target ranges. -/
theorem cumulativeLeastPrime_le_fourNinths
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ fourNinthsCumulativeEnvelope N := by
  exact
    cumulativeLeastPrime_le_base fourNinthsHistoryBase fourNinthsHistoryBase_nonneg
      (fun hn ho hc L hlog ↦ leastPrime_le_fourNinthsScale hGRH hn ho hc L hlog) historyProfiles
      hGRH N

/-- The four-ninths cumulative envelope never exceeds the preceding tightened Gaussian
history envelope. This follows from monotonicity of the history construction. -/
theorem fourNinthsCumulative_le_tight (N : ℕ) :
    fourNinthsCumulativeEnvelope N ≤ gaussianTightCumulativeEnvelope N := by
  apply baseHistory_mono TriangularProfile.T TriangularProfile.C
  intro L
  exact min_le_left _ _

/-- The complete history envelope is at most four ninths of the squared
logarithm at every natural endpoint. Project the common-scale base through
the history recurrence and then project its four-ninths component. -/
theorem fourNinthsCumulative_le_log_sq (N : ℕ) :
    fourNinthsCumulativeEnvelope N ≤ (4 / 9 : ℝ) * (Real.log N) ^ 2 := by
  exact
    (baseHistory_le_base TriangularProfile.T TriangularProfile.C fourNinthsHistoryBase
          historyProfiles (Real.log N)).trans
      (min_le_right _ _)

/-- Under GRH the cumulative maximum of least rejecting primes through `N`
is at most four ninths of the squared logarithm of `N`. The common-scale
history covers every earlier input, including empty target ranges. -/
theorem cumulativeLeastPrime_le_four_ninths_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ (4 / 9 : ℝ) * (Real.log N) ^ 2 := by
  exact (cumulativeLeastPrime_le_fourNinths hGRH N).trans (fourNinthsCumulative_le_log_sq N)

end PseudoPrime.PrimeTestBounds.MillerRabin
