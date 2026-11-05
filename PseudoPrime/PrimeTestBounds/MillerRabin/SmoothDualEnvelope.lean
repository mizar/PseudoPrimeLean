/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmoothDualSeries
public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleComparison
/-! # Public pointwise envelope with the continuous dual-scale candidate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Intersect the certified dual selection with the continuous witness series. -/
noncomputable def smoothSelected (n : ℕ) : ℝ :=
  if (80000 : ℝ) ≤ Real.log n then
    min (dualSelected n) (smoothSeriesCoeff (Real.log n) * Real.log n ^ 2)
  else dualSelected n
/-- Prime rounding of the continuous-candidate selection. -/
noncomputable def smoothPrime (n : ℕ) : ℝ := primeRound (smoothSelected n)
/-- The continuous-candidate selection is no greater than the previous selection. -/
theorem smoothSelected_le (n : ℕ) : smoothSelected n ≤ dualSelected n := by
  unfold smoothSelected
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl
/-- Under GRH, the least rejecting prime is below both witness bounds. -/
theorem exists_least_smoothSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ smoothSelected n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_dualSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (80000 : ℝ) ≤ Real.log n
  · rw [smoothSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := smoothSeries_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [smoothSelected, ite_eq_right hL]
    exact hb
/-- Under GRH, prime rounding preserves the least rejecting prime. -/
theorem exists_least_smoothPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ smoothPrime n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_smoothSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩
/-- Both cutoffs retain the value three on the certified small interval. -/
theorem smooth_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    smoothSelected n = 3 ∧ smoothPrime n = 3 := by
  have hlog : Real.log n < 80000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have he : smoothSelected n = dualSelected n := ite_eq_right (not_le_of_gt hlog)
  have hh := dual_small_three hl hu
  constructor
  · exact he.trans hh.1
  · change primeRound (smoothSelected n) = 3
    rw [he]
    exact hh.2
/-- The selection is monotone on the small interval because it is constant there. -/
theorem smooth_small_mono : MonotoneOn smoothSelected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [(smooth_small_three hm.1 hm.2).1, (smooth_small_three hn.1 hn.2).1]
/-- The new selection strictly improves the preceding full public minimum
on the certified interval. -/
theorem smoothSelected_lt_reduced {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 14000000) : smoothSelected n < reducedSelected n := by
  exact (smoothSelected_le n).trans_lt (dualSelected_lt_reduced_window hL hU)
end PseudoPrime.PrimeTestBounds.MillerRabin
