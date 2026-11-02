/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTightBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHistoryCaps

/-! # Candidate-A cumulative MR bounds with inherited Gaussian history caps

Candidate A supplies its own actual common-scale base. Base-order preservation makes its
whole-domain cumulative value no larger than the established residual-7.6 Gaussian history.
All earlier rational entrance and recovery caps transfer unchanged. This consumer imports
history downstream of actual witnesses; pointwise witness and comparison leaves stay separate.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect log scale squared with candidate A at the safe covering scale max(63,L).
Input: any real upper log scale. Output: a common-scale base for the final cumulative bound.
The existing positive floor covers inputs preceding the actual analytic entrance. -/
noncomputable def gaussianTightHistoryBase (L : ℝ) : ℝ :=
  min (L ^ 2) (gaussianTightBound (max 63 L))

/-- Evaluate the eight-profile MR history with candidate A as its common-scale base.
Input: every natural endpoint, including empty target ranges. Output: the final tighter
cumulative majorant, keeping the true least rejecting-prime definition unchanged. -/
noncomputable def gaussianTightCumulativeEnvelope (N : ℕ) : ℝ :=
  baseHistory TriangularProfile.T TriangularProfile.C gaussianTightHistoryBase historyProfiles
    (Real.log N)

/-- At every real scale, the candidate-A history base is nonnegative.
Intersect the square with the unchanged positive Gaussian cutoff floor. -/
theorem gaussianTightHistoryBase_nonneg (L : ℝ) : 0 ≤ gaussianTightHistoryBase L := by
  exact
    le_min (sq_nonneg L)
      ((by norm_num only : (0 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
        (gaussianTight_cutoff_floor _))

/-- At every real scale, the candidate-A base is below the established residual-7.6 base.
Intersect its global cutoff comparison with the identical square term. -/
theorem gaussianTightHistoryBase_le_gaussian (L : ℝ) :
    gaussianTightHistoryBase L ≤ gaussianHistoryBase L := by
  exact min_le_min le_rfl (gaussianTight_le_surplus _)

/-- Under GRH, candidate A at max(63,L) covers every odd composite with log n at most L.
Above entrance use its actual witness and monotonicity; below entrance absorb the existing
log-square witness using the unchanged cutoff floor. This closes the all-input scale contract. -/
theorem leastPrime_le_gaussianTightScale
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ gaussianTightBound (max 63 L) := by
  by_cases h63 : 63 ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := exists_prime_gaussianTight ho hc hGRH h63
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    exact ((Nat.cast_le.mpr hm).trans hb).trans (gaussianTight_mono (hlog.trans (le_max_right _ _)))
  · have hs :=
      (sq_le_sq₀ (Real.log_natCast_nonneg n) (by norm_num only : (0 : ℝ) ≤ 63)).mpr
        (le_of_not_ge h63)
    have hf := gaussianTight_cutoff_floor (max 63 L)
    exact
      (compositeLeastPrime_le_log_sq hGRH hn ho hc).trans
        (hs.trans ((by norm_num only : (63 : ℝ) ^ 2 ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans hf))

/-- Under GRH, the candidate-A base bounds the actual least rejecting prime at any covering scale.
Intersect the existing log-square bound and the entrance-safe candidate-A bound. -/
theorem leastPrime_le_gaussianTightBase
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ gaussianTightHistoryBase L := by
  have h0 := Real.log_natCast_nonneg n
  exact
    le_min
      ((compositeLeastPrime_le_log_sq hGRH hn ho hc).trans
        ((sq_le_sq₀ h0 (h0.trans hlog)).mpr hlog))
      (leastPrime_le_gaussianTightScale hGRH hn ho hc L hlog)

/-- Under GRH, candidate A bounds the cumulative least rejecting prime at every natural endpoint.
Apply the already proved arbitrary-base transfer with its internally supplied scale contract. -/
theorem cumulativeLeastPrime_le_gaussianTight
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ gaussianTightCumulativeEnvelope N := by
  exact
    cumulativeLeastPrime_le_base gaussianTightHistoryBase gaussianTightHistoryBase_nonneg
      (fun hn ho hc L hlog ↦ leastPrime_le_gaussianTightBase hGRH hn ho hc L hlog) historyProfiles
      hGRH N

/-- At every endpoint, the final cumulative envelope is below the earlier Gaussian history.
Use the global base comparison and recurrence order preservation; GRH is not needed. -/
theorem gaussianTightCumulative_le_gaussian (N : ℕ) :
    gaussianTightCumulativeEnvelope N ≤ gaussianCumulativeEnvelope N := by
  exact
    baseHistory_mono TriangularProfile.T TriangularProfile.C gaussianTightHistoryBase
      gaussianHistoryBase gaussianTightHistoryBase_le_gaussian historyProfiles (Real.log N)

/-- The final cumulative envelope retains the full former square-base history guarantee.
Compose candidate-A non-worsening with the existing whole-history comparison. -/
theorem gaussianTightCumulative_le_history (N : ℕ) :
    gaussianTightCumulativeEnvelope N ≤ historyCumulativeEnvelope N := by
  exact (gaussianTightCumulative_le_gaussian N).trans (gaussianCumulative_le_history N)

/-- The final cumulative envelope retains strict improvement on the closed log band [100,101].
Compose base-order preservation with the earlier full-history strict comparison. -/
theorem gaussianTightCumulative_lt_history {N : ℕ} (hL : 100 ≤ Real.log N) (hU : Real.log N ≤ 101) :
    gaussianTightCumulativeEnvelope N < historyCumulativeEnvelope N := by
  exact (gaussianTightCumulative_le_gaussian N).trans_lt (gaussianCumulative_lt_history hL hU)

/-- Candidate A inherits the first Gaussian history cap 59/125 times the entrance square.
Use its smaller base; no new root certificate is required. -/
theorem gaussianTightBase_first_cap :
    gaussianTightHistoryBase 30000000000 < (59 / 125 : ℝ) * (30000000000 : ℝ) ^ 2 := by
  exact (gaussianTightHistoryBase_le_gaussian _).trans_lt gaussianBase_first_cap

/-- Candidate A inherits the .4603 cap at the second entrance after the first profile.
Apply recurrence order preservation to the exact older second-entrance history. -/
theorem gaussianTightHistory_second_cap :
    baseHistory TriangularProfile.T TriangularProfile.C gaussianTightHistoryBase [triangularP04603]
        40000000000 ≤
      (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 := by
  exact
    (baseHistory_mono TriangularProfile.T TriangularProfile.C gaussianTightHistoryBase
          gaussianHistoryBase gaussianTightHistoryBase_le_gaussian [triangularP04603]
          40000000000).trans_eq
      gaussianHistory_second_entry

/-- Whenever the first inherited cap fits the .4603 quadratic, the final cumulative value does too.
Transfer the complete eight-profile recovery theorem through base non-worsening. -/
theorem gaussianTight_first_recovered {N : ℕ}
    (hr : (59 / 125 : ℝ) * (30000000000 : ℝ) ^ 2 ≤ (4603 / 10000 : ℝ) * Real.log N ^ 2) :
    gaussianTightCumulativeEnvelope N ≤ (4603 / 10000 : ℝ) * Real.log N ^ 2 := by
  exact (gaussianTightCumulative_le_gaussian N).trans (gaussian_first_recovered hr)

/-- Whenever the second inherited cap fits the .4145 quadratic, the final cumulative value does too.
Transfer the complete recovery theorem without recalculating its numerical certificate. -/
theorem gaussianTight_second_recovered {N : ℕ}
    (hr : (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 ≤ (4145 / 10000 : ℝ) * Real.log N ^ 2) :
    gaussianTightCumulativeEnvelope N ≤ (4145 / 10000 : ℝ) * Real.log N ^ 2 := by
  exact (gaussianTightCumulative_le_gaussian N).trans (gaussian_second_recovered hr)

/-- From log scale 30378881000, candidate A retains the .4603 whole-history bound.
Reuse the established exact integer recovery scale through cumulative non-worsening. -/
theorem gaussianTight_first_recovery_scale {N : ℕ} (hL : 30378881000 ≤ Real.log N) :
    gaussianTightCumulativeEnvelope N ≤ (4603 / 10000 : ℝ) * Real.log N ^ 2 := by
  exact (gaussianTightCumulative_le_gaussian N).trans (gaussian_first_recovery_scale hL)

/-- From log scale 42152002600, candidate A retains the .4145 whole-history bound.
Reuse the established exact integer recovery scale through cumulative non-worsening. -/
theorem gaussianTight_second_recovery_scale {N : ℕ} (hL : 42152002600 ≤ Real.log N) :
    gaussianTightCumulativeEnvelope N ≤ (4145 / 10000 : ℝ) * Real.log N ^ 2 := by
  exact (gaussianTightCumulative_le_gaussian N).trans (gaussian_second_recovery_scale hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
