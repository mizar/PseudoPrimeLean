/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmoothDualMonotone
public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleCumulative
/-! # Entrance-safe cumulative history for the continuous candidate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Combine the previous history with the continuous bridge and its Gaussian tail,
retaining entrance bounds. -/
noncomputable def smoothHistory (L : ℝ) : ℝ :=
  min (dualGaussianHistory L)
    (max (dualHistory6 5000000)
      (if 200000000 ≤ L then
        max (smoothCoeff 200000000 * (200000000 : ℝ) ^ 2)
          ((21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2)
      else smoothCoeff L * L ^ 2))
/-- The continuous-candidate history is nonnegative on every real scale. -/
theorem smoothHistory_nonneg : ∀ L, 0 ≤ smoothHistory L := by
  intro L
  exact le_min (dualGaussianHistory_nonneg L) ((dualHistory_nonneg 5000000).trans (le_max_left _ _))
/-- Under GRH, the history bounds each least witness below the common scale.
Separate inputs before the entrance, on the continuous bridge, and in the Gaussian tail. -/
theorem leastPrime_le_smoothScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ smoothHistory L := by
  refine le_min (leastPrime_le_dualGaussianScale hGRH hn ho hc L hlog) ?_
  by_cases hlow : (5000000 : ℝ) ≤ Real.log n
  · by_cases hnG : (200000000 : ℝ) ≤ Real.log n
    · have hLG : (200000000 : ℝ) ≤ L := hnG.trans hlog
      rw [ite_eq_left hLG]
      obtain ⟨p, hp, hb, hr⟩ := prime_witness_dualGaussian hn ho hc hGRH hnG
      have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
      have ha : 0 ≤ adaptiveGaussianA (Real.log n) := by
        have hh := dualGaussian_slope_lower (Real.log n) hnG
        linarith only [hh]
      have hs := pow_le_pow_left₀ (mul_nonneg ha (by linarith only [hnG]))
        (dualGaussian_scaled_mono hnG hlog) 2
      have hh := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 21 / 10)
      rw [mul_pow] at hh
      have hh' : (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 * Real.log n ^ 2 ≤
          (21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2 := by
        simpa only [mul_assoc] using hh
      exact ((Nat.cast_le.mpr hm).trans hb).trans
        (hh'.trans ((le_max_right _ _).trans (le_max_right _ _)))
    · obtain ⟨p, hp, hb, hr⟩ :=
        prime_witness_smoothDual hn ho hc hGRH hlow (le_of_not_ge hnG)
      have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
      by_cases hLG : (200000000 : ℝ) ≤ L
      · rw [ite_eq_left hLG]
        have hs := smoothCutoff_mono hlow (le_of_not_ge hnG)
        exact ((Nat.cast_le.mpr hm).trans hb).trans
          (hs.trans ((le_max_left _ _).trans (le_max_right _ _)))
      · rw [ite_eq_right hLG]
        have hs := smoothCutoff_mono hlow hlog
        exact ((Nat.cast_le.mpr hm).trans hb).trans (hs.trans (le_max_right _ _))
  · exact (leastPrime_le_dualHistory hGRH hn ho hc 5000000 (le_of_not_ge hlow)).trans
      (le_max_left _ _)
/-- Intersect the previous cumulative bound with the continuous history. -/
noncomputable def smoothCumulative (N : ℕ) : ℝ :=
  min (dualCumulative N) (smoothHistory (Real.log N))
/-- Under GRH, the continuous-candidate cumulative bound controls every endpoint. -/
theorem cumulativeLeastPrime_le_smooth
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ smoothCumulative N := by
  apply le_min (cumulativeLeastPrime_le_dual hGRH N)
  have h := cumulativeLeastPrime_le_base smoothHistory smoothHistory_nonneg
    (fun hn ho hc L hlog ↦ leastPrime_le_smoothScale hGRH hn ho hc L hlog) [] hGRH N
  simpa only [baseHistory] using h
end PseudoPrime.PrimeTestBounds.MillerRabin
