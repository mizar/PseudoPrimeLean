/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedFixedCumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedFixedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourCumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourSeries

/-! # Reduced-contour pointwise and cumulative Miller–Rabin bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the existing selection with the certified reduced series after its entrance. -/
noncomputable def reducedSelected (n : ℕ) : ℝ :=
  if (80000 : ℝ) ≤ Real.log n then
    min (fixedImprovedSelected n) (reducedSeriesCoeff (Real.log n) * Real.log n ^ 2)
  else fixedImprovedSelected n

/-- The combined pointwise selection is never larger than the preceding selection. -/
theorem reducedSelected_le (n : ℕ) : reducedSelected n ≤ fixedImprovedSelected n := by
  unfold reducedSelected
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- Below the new entrance the earlier pointwise selection is unchanged. -/
theorem reducedSelected_eq {n : ℕ} (hL : Real.log n < 80000) :
    reducedSelected n = fixedImprovedSelected n := by exact ite_eq_right (not_le_of_gt hL)

/-- Under GRH, the least rejecting prime lies below the combined selection.
Transfer the new actual witness bound by leastness and retain the previous bound. -/
theorem exists_least_reducedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ reducedSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_fixedImproved hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (80000 : ℝ) ≤ Real.log n
  · rw [reducedSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := reducedSeries_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [reducedSelected, ite_eq_right hL]
    exact hb

/-- Round the combined real cutoff down to its greatest eligible prime. -/
noncomputable def reducedPrime (n : ℕ) : ℝ :=
  primeRound (reducedSelected n)

/-- Under GRH, prime rounding retains the least rejecting prime in the combined cutoff. -/
theorem exists_least_reducedPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ reducedPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_reducedSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Both combined cutoffs retain the value three on the certified small interval.
The new entrance lies above the entire interval, so the earlier result applies unchanged. -/
theorem reduced_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    reducedSelected n = 3 ∧ reducedPrime n = 3 := by
  have hlog : Real.log n < 80000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have he : reducedSelected n = fixedImprovedSelected n := ite_eq_right (not_le_of_gt hlog)
  have hh := fixedImproved_small_three hl hu
  constructor
  · exact he.trans hh.1
  · change primeRound (reducedSelected n) = 3
    rw [he]
    exact hh.2

/-- Intersect the preceding cumulative bound with the entrance-safe reduced history. -/
noncomputable def reducedCumulative (N : ℕ) : ℝ :=
  min (fixedImprovedCumulative N) (reducedGaussianHistory (Real.log N))

/-- The combined cumulative bound is no larger than the previous cumulative bound. -/
theorem reducedCumulative_le (N : ℕ) : reducedCumulative N ≤ fixedImprovedCumulative N := by
  exact min_le_left _ _

/-- Under GRH, the combined cumulative bound controls every least witness through the endpoint.
The reduced history covers inputs before each new entrance. -/
theorem cumulativeLeastPrime_le_reduced
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ reducedCumulative N := by
  apply le_min (cumulativeLeastPrime_le_fixedImproved hGRH N)
  have h :=
    cumulativeLeastPrime_le_base reducedGaussianHistory reducedGaussianHistory_nonneg
      (fun hn ho hc L hlog ↦ leastPrime_le_reducedGaussianScale hGRH hn ho hc L hlog) [] hGRH N
  simpa only [baseHistory] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
