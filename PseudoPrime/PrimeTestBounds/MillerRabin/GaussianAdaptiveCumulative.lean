/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveMonotone
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveEnvelope

/-! # Cumulative adaptive Gaussian envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common-scale cap retains the triangular entrance history and the scaled Gaussian cutoff. -/
noncomputable def gaussianAdaptiveCap (L : ℝ) : ℝ :=
  max (triangularAdaptiveCap 2000000000000) ((21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2)

/-- Under GRH, the Gaussian cap bounds the least rejecting prime at every smaller input. -/
theorem leastPrime_le_adaptiveGaussianScale
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ gaussianAdaptiveCap L := by
  by_cases hhigh : (2000000000000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := gaussianAdaptive_prime_witness hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have ha : 0 ≤ adaptiveGaussianA (Real.log n) := by
      have hh := adaptiveGaussianA_lower _ hhigh
      linarith only [hh]
    have hs :=
      pow_le_pow_left₀ (mul_nonneg ha (by linarith only [hhigh]))
        (adaptiveGaussian_scaled_mono hhigh hlog) 2
    have hh := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 21 / 10)
    rw [mul_pow] at hh
    have hh' :
      (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 * Real.log n ^ 2 ≤
        (21 / 10 : ℝ) * (adaptiveGaussianA L * L) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact ((Nat.cast_le.mpr hm).trans hb).trans (hh'.trans (le_max_right _ _))
  · have hprev := leastPrime_le_triangularScale hGRH hn ho hc 2000000000000 (le_of_not_ge hhigh)
    exact hprev.trans (le_max_left _ _)

/-- The cumulative envelope retains both the earlier bound and the Gaussian cap. -/
noncomputable def gaussianAdaptiveCumulative (N : ℕ) : ℝ :=
  min (triangularAdaptiveCumulative N) (gaussianAdaptiveCap (Real.log N))

/-- Under GRH, the cumulative maximum least witness is bounded by the Gaussian envelope. -/
theorem cumulativeLeastPrime_le_gaussianAdaptive
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ gaussianAdaptiveCumulative N := by
  have hcap : ∀ L, 0 ≤ gaussianAdaptiveCap L := by
    intro L
    have h0 : (0 : ℝ) ≤ (4 / 9) * (30000000000 : ℝ) ^ 2 := by norm_num only
    exact h0.trans ((le_max_left _ _).trans (le_max_left _ _))
  have h :=
    cumulativeLeastPrime_le_base gaussianAdaptiveCap hcap
      (fun hn ho hc L hlog ↦ leastPrime_le_adaptiveGaussianScale hGRH hn ho hc L hlog) [] hGRH N
  have h' : (cumulativeLeastPrime N : ℝ) ≤ gaussianAdaptiveCap (Real.log N) := by
    simpa only [baseHistory] using h
  exact le_min (cumulativeLeastPrime_le_triangular hGRH N) h'

end PseudoPrime.PrimeTestBounds.MillerRabin
