/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualMeanBridge
public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleSeries
/-! # Combine the two-cell mean witness with the dual-scale series -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Add the 4187/10000 mean bound above its entrance to the dual-scale series. -/
noncomputable def dualMeanSeriesCoeff (L : ℝ) : ℝ :=
  if 81000 ≤ L then min (dualSeriesCoeff L) (4187 / 10000)
  else dualSeriesCoeff L
/-- Under GRH, the least rejecting prime transfers both actual witness bounds to
the minimum coefficient for every odd composite above scale 80000. -/
theorem dualMeanSeries_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ dualMeanSeriesCoeff (Real.log n) * Real.log n ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h : (81000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hr, _, hpmin⟩ := exists_least_reducedSelected hn ho hc hGRH
    obtain ⟨q, hq, hqb, hqr⟩ := dualSeries_witness hn ho hc hGRH hL
    obtain ⟨r, hrp, hrb, hrr⟩ := prime_witness_04187 hn ho hc hGRH h
    refine ⟨p, hp, ?_, hr⟩
    rw [dualMeanSeriesCoeff, ite_eq_left h, min_mul_of_nonneg _ _ (sq_nonneg _)]
    exact le_min ((Nat.cast_le.mpr (hpmin q hq hqr)).trans hqb)
      ((Nat.cast_le.mpr (hpmin r hrp hrr)).trans hrb)
  · rw [dualMeanSeriesCoeff, ite_eq_right h]
    exact dualSeries_witness hn ho hc hGRH hL

/-- The mean-adjusted normalized coefficient remains nonincreasing across its entrance. -/
theorem dualMeanSeries_antitone {L M : ℝ} (hLM : L ≤ M) :
    dualMeanSeriesCoeff M ≤ dualMeanSeriesCoeff L := by
  unfold dualMeanSeriesCoeff
  by_cases hL : (81000 : ℝ) ≤ L
  · have hM := hL.trans hLM
    rw [ite_eq_left hL, ite_eq_left hM]
    exact min_le_min_right _ (dualSeries_antitone hLM)
  · by_cases hM : (81000 : ℝ) ≤ M
    · rw [ite_eq_right hL, ite_eq_left hM]
      exact (min_le_left _ _).trans (dualSeries_antitone hLM)
    · rw [ite_eq_right hL, ite_eq_right hM]
      exact dualSeries_antitone hLM
end PseudoPrime.PrimeTestBounds.MillerRabin
