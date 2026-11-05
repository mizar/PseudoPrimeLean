/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleEnvelope
/-! # Entrance-safe cumulative dual-scale bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Add the 1th certified quadratic bound, retaining the earlier entrance history. -/
noncomputable def dualHistory1 : ℝ → ℝ :=
  reducedHistoryStep reducedGaussianHistory 81000 (4187 / 10000)
/-- Add the 2th certified quadratic bound, retaining the earlier entrance history. -/
noncomputable def dualHistory2 : ℝ → ℝ := reducedHistoryStep dualHistory1 5000000 (2 / 5)
/-- Add the 3th certified quadratic bound, retaining the earlier entrance history. -/
noncomputable def dualHistory3 : ℝ → ℝ := reducedHistoryStep dualHistory2 15000000 (9 / 25)
/-- Add the 4th certified quadratic bound, retaining the earlier entrance history. -/
noncomputable def dualHistory4 : ℝ → ℝ := reducedHistoryStep dualHistory3 30000000 (33 / 100)
/-- Add the 5th certified quadratic bound, retaining the earlier entrance history. -/
noncomputable def dualHistory5 : ℝ → ℝ := reducedHistoryStep dualHistory4 60000000 (31 / 100)
/-- Add the 6th certified quadratic bound, retaining the earlier entrance history. -/
noncomputable def dualHistory6 : ℝ → ℝ := reducedHistoryStep dualHistory5 100000000 (29 / 100)
/-- Each quadratic history bound remains nonnegative. -/
theorem dualHistory_nonneg : ∀ L, 0 ≤ dualHistory6 L := by
  exact reducedStep_nonneg
    (reducedStep_nonneg (reducedStep_nonneg (reducedStep_nonneg
      (reducedStep_nonneg (reducedStep_nonneg reducedGaussianHistory_nonneg (by norm_num only))
        (by norm_num only)) (by norm_num only)) (by norm_num only)) (by norm_num only))
    (by norm_num only)
/-- Under GRH, the fixed history covers every least witness below the common scale. -/
theorem leastPrime_le_dualHistory (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ dualHistory6 L := by
  have h1 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ dualHistory1 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH
      (fun hn ho hc L hlog ↦ leastPrime_le_reducedGaussianScale hGRH hn ho hc L hlog)
      (fun hn ho hc hL ↦ prime_witness_04187 hn ho hc hGRH hL) hn ho hc L hlog
  have h2 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ dualHistory2 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h1
      (fun hn ho hc hL ↦ prime_witness_dual040 hn ho hc hGRH hL) hn ho hc L hlog
  have h3 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ dualHistory3 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h2
      (fun hn ho hc hL ↦ prime_witness_dual036 hn ho hc hGRH hL) hn ho hc L hlog
  have h4 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ dualHistory4 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h3
      (fun hn ho hc hL ↦ prime_witness_dual033 hn ho hc hGRH hL) hn ho hc L hlog
  have h5 : ∀ {n : ℕ}, 1 < n → Odd n → ¬n.Prime → ∀ L, Real.log n ≤ L →
      (compositeLeastPrime n : ℝ) ≤ dualHistory5 L := by
    intro n hn ho hc L hlog
    exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h4
      (fun hn ho hc hL ↦ prime_witness_dual031 hn ho hc hGRH hL) hn ho hc L hlog
  exact reducedStep_bound (by norm_num only) (by norm_num only) hGRH h5
    (fun hn ho hc hL ↦ prime_witness_dual029 hn ho hc hGRH hL) hn ho hc L hlog
/-- Intersect the fixed history with the Gaussian candidate and its entrance history. -/
noncomputable def dualGaussianHistory (L : ℝ) : ℝ :=
  min (dualHistory6 L)
    (max (dualHistory6 200000000) ((21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2))
/-- The Gaussian history is nonnegative at every real scale. -/
theorem dualGaussianHistory_nonneg : ∀ L, 0 ≤ dualGaussianHistory L := by
  intro L
  exact le_min (dualHistory_nonneg L)
    ((mul_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 10) (sq_nonneg _)).trans (le_max_right _ _))
/-- Under GRH, the Gaussian history bounds all least witnesses below the common scale. -/
theorem leastPrime_le_dualGaussianScale
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ dualGaussianHistory L := by
  refine le_min (leastPrime_le_dualHistory hGRH hn ho hc L hlog) ?_
  by_cases hhigh : (200000000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := prime_witness_dualGaussian hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have ha : 0 ≤ adaptiveGaussianA (Real.log n) := by
      have hh := dualGaussian_slope_lower (Real.log n) hhigh
      linarith only [hh]
    have hs := pow_le_pow_left₀ (mul_nonneg ha (by linarith only [hhigh]))
      (dualGaussian_scaled_mono hhigh hlog) 2
    have hh := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 21 / 10)
    rw [mul_pow] at hh
    have hh' : (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 * Real.log n ^ 2 ≤
        (21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact ((Nat.cast_le.mpr hm).trans hb).trans (hh'.trans (le_max_right _ _))
  · exact
      (leastPrime_le_dualHistory hGRH hn ho hc 200000000 (le_of_not_ge hhigh)).trans
        (le_max_left _ _)
/-- Intersect the preceding cumulative bound with the new entrance-safe history. -/
noncomputable def dualCumulative (N : ℕ) : ℝ :=
  min (reducedCumulative N) (dualGaussianHistory (Real.log N))
/-- Under GRH, the combined bound controls the cumulative least rejecting prime. -/
theorem cumulativeLeastPrime_le_dual
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ dualCumulative N := by
  apply le_min (cumulativeLeastPrime_le_reduced hGRH N)
  have h := cumulativeLeastPrime_le_base dualGaussianHistory dualGaussianHistory_nonneg
    (fun hn ho hc L hlog ↦ leastPrime_le_dualGaussianScale hGRH hn ho hc L hlog) [] hGRH N
  simpa only [baseHistory] using h
end PseudoPrime.PrimeTestBounds.MillerRabin
