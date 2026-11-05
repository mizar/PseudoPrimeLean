/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmoothDualWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleEnvelope
/-! # Continuous and fixed normalized witness series -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Use the continuous coefficient until the earlier Gaussian entrance and Gaussian thereafter. -/
noncomputable def smoothCandidateCoeff (L : ℝ) : ℝ :=
  if 200000000 ≤ L then (21 / 10) * adaptiveGaussianA L ^ 2 else smoothCoeff L
/-- At the Gaussian entrance the new Gaussian coefficient is no larger than the continuous bound. -/
theorem smoothCandidate_switch :
    (21 / 10 : ℝ) * adaptiveGaussianA 200000000 ^ 2 ≤ smoothCoeff 200000000 := by
  have ha := dualGaussian_slope_lower 200000000 (by norm_num only)
  have hb := dualGaussian_slope_upper 200000000 (by norm_num only)
  have hc := smoothGaussian_radius_lower 200000000 (by norm_num only) (by norm_num only)
  have hs : adaptiveGaussianA 200000000 ^ 2 ≤ smoothGaussian_radius 200000000 ^ 2 :=
    pow_le_pow_left₀ (by linarith only [ha]) (by linarith only [hb, hc]) 2
  exact (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 21 / 10)).trans
    (le_max_right _ _)
/-- The continuous-to-Gaussian coefficient is nonincreasing from its entrance. -/
theorem smoothCandidate_antitone {L M : ℝ} (hL : 5000000 ≤ L) (hLM : L ≤ M) :
    smoothCandidateCoeff M ≤ smoothCandidateCoeff L := by
  unfold smoothCandidateCoeff
  by_cases hA : (200000000 : ℝ) ≤ L
  · have hB := hA.trans hLM
    rw [ite_eq_left hA, ite_eq_left hB]
    exact dualGaussian_coeff_anti hA hLM
  · by_cases hB : (200000000 : ℝ) ≤ M
    · rw [ite_eq_right hA, ite_eq_left hB]
      exact (dualGaussian_coeff_anti (by norm_num only : (200000000 : ℝ) ≤ 200000000) hB).trans
        (smoothCandidate_switch.trans (smoothCoeff_anti hL (le_of_not_ge hA)))
    · rw [ite_eq_right hA, ite_eq_right hB]
      exact smoothCoeff_anti hL hLM
/-- Under GRH, the continuous-to-Gaussian candidate gives an actual rejecting prime. -/
theorem smoothCandidate_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ smoothCandidateCoeff (Real.log n) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hG : (200000000 : ℝ) ≤ Real.log n
  · rw [smoothCandidateCoeff, ite_eq_left hG]
    exact prime_witness_dualGaussian hn ho hc hGRH hG
  · rw [smoothCandidateCoeff, ite_eq_right hG]
    exact prime_witness_smoothDual hn ho hc hGRH hL (le_of_not_ge hG)
/-- Combine the fixed and continuous coefficients at the continuous entrance. -/
noncomputable def smoothSeriesCoeff (L : ℝ) : ℝ :=
  if 5000000 ≤ L then min (dualMeanSeriesCoeff L) (smoothCandidateCoeff L)
  else dualMeanSeriesCoeff L
/-- The combined normalized coefficient is nonincreasing. -/
theorem smoothSeries_antitone {L M : ℝ} (hLM : L ≤ M) :
    smoothSeriesCoeff M ≤ smoothSeriesCoeff L := by
  unfold smoothSeriesCoeff
  by_cases hL : (5000000 : ℝ) ≤ L
  · have hM := hL.trans hLM
    rw [ite_eq_left hL, ite_eq_left hM]
    exact min_le_min (dualMeanSeries_antitone hLM) (smoothCandidate_antitone hL hLM)
  · by_cases hM : (5000000 : ℝ) ≤ M
    · rw [ite_eq_right hL, ite_eq_left hM]
      exact (min_le_left _ _).trans (dualMeanSeries_antitone hLM)
    · rw [ite_eq_right hL, ite_eq_right hM]
      exact dualMeanSeries_antitone hLM
/-- Under GRH, the least rejecting prime transfers both actual witness bounds
to the combined series. -/
theorem smoothSeries_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ smoothSeriesCoeff (Real.log n) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h : (5000000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hr, _, hpmin⟩ := exists_least_dualSelected hn ho hc hGRH
    obtain ⟨q, hq, hqb, hqr⟩ := dualMeanSeries_witness hn ho hc hGRH hL
    obtain ⟨r, hrp, hrb, hrr⟩ := smoothCandidate_witness hn ho hc hGRH h
    refine ⟨p, hp, ?_, hr⟩
    rw [smoothSeriesCoeff, ite_eq_left h, min_mul_of_nonneg _ _ (sq_nonneg _)]
    exact le_min ((Nat.cast_le.mpr (hpmin q hq hqr)).trans hqb)
      ((Nat.cast_le.mpr (hpmin r hrp hrr)).trans hrb)
  · rw [smoothSeriesCoeff, ite_eq_right h]
    exact dualMeanSeries_witness hn ho hc hGRH hL
end PseudoPrime.PrimeTestBounds.MillerRabin
