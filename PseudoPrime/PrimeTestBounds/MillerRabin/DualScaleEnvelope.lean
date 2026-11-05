/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualMeanSeries
/-! # Public pointwise dual-scale witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- Intersect the existing selection with the dual mean series at its entrance. -/
noncomputable def dualSelected (n : ℕ) : ℝ :=
  if (80000 : ℝ) ≤ Real.log n then
    min (reducedSelected n) (dualMeanSeriesCoeff (Real.log n) * Real.log n ^ 2)
  else reducedSelected n
/-- Round the dual-scale real selection to an eligible prime. -/
noncomputable def dualPrime (n : ℕ) : ℝ := primeRound (dualSelected n)
/-- The new selection is no greater than the preceding selection. -/
theorem dualSelected_le (n : ℕ) : dualSelected n ≤ reducedSelected n := by
  unfold dualSelected
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl
/-- Under GRH, the least rejecting prime is below both actual witness bounds. -/
theorem exists_least_dualSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ dualSelected n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_reducedSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (80000 : ℝ) ≤ Real.log n
  · rw [dualSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := dualMeanSeries_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [dualSelected, ite_eq_right hL]
    exact hb
/-- Under GRH, prime rounding preserves the least rejecting prime. -/
theorem exists_least_dualPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ dualPrime n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_dualSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩
/-- Both new cutoffs retain the value three on the certified small interval. -/
theorem dual_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    dualSelected n = 3 ∧ dualPrime n = 3 := by
  have hlog : Real.log n < 80000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have he : dualSelected n = reducedSelected n := ite_eq_right (not_le_of_gt hlog)
  have hh := reduced_small_three hl hu
  constructor
  · exact he.trans hh.1
  · change primeRound (dualSelected n) = 3
    rw [he]
    exact hh.2
/-- The new pointwise selection is monotone on the small interval because it is constant there. -/
theorem dualSelected_small_mono : MonotoneOn dualSelected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [(dual_small_three hm.1 hm.2).1, (dual_small_three hn.1 hn.2).1]
end PseudoPrime.PrimeTestBounds.MillerRabin
