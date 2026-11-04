/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveWitness

/-! # Pointwise envelope with the scale-dependent triangular witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pointwise cutoff adds the adaptive triangular candidate at logarithmic scale
`3 * 10 ^ 10`. Below its entrance the preceding mean-selected cutoff is retained.
This combines the new actual witness with all earlier candidates. -/
noncomputable def triangularAdaptiveSelected (n : ℕ) : ℝ :=
  if (30000000000 : ℝ) ≤ Real.log n then
    min (meanSelected n) ((triangularAdaptiveRadius (Real.log n)) ^ 2 * (Real.log n) ^ 2)
  else meanSelected n

/-- Prime rounding of the adaptive cutoff preserves every prime below it.
This is the prime-rounded version of the pointwise envelope. -/
noncomputable def triangularAdaptivePrime (n : ℕ) : ℝ :=
  primeRound (triangularAdaptiveSelected n)

/-- The adaptive cutoff is at most the preceding mean-selected cutoff.
It either takes a minimum with the new candidate or retains the previous value. -/
theorem triangularAdaptiveSelected_le (n : ℕ) : triangularAdaptiveSelected n ≤ meanSelected n := by
  by_cases h : (30000000000 : ℝ) ≤ Real.log n
  · rw [triangularAdaptiveSelected, ite_eq_left h]
    exact min_le_left _ _
  · rw [triangularAdaptiveSelected, ite_eq_right h]

/-- Below logarithmic scale `3 * 10 ^ 10`, the adaptive cutoff equals the
mean-selected cutoff. This preserves all previous small-input behavior. -/
theorem triangularAdaptiveSelected_eq {n : ℕ} (h : Real.log n < 30000000000) :
    triangularAdaptiveSelected n = meanSelected n := by exact ite_eq_right (not_le_of_gt h)

/-- For `2047 ≤ n < 3000`, both the adaptive cutoff and its prime-rounded version
remain three. The adaptive branch is inactive and three is fixed by prime rounding.
This preserves the public small-input convention. -/
theorem triangularAdaptive_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    triangularAdaptiveSelected n = 3 ∧ triangularAdaptivePrime n = 3 := by
  have h : Real.log n < 30000000000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have he : triangularAdaptiveSelected n = 3 :=
    (triangularAdaptiveSelected_eq h).trans (meanSelected_small_three hl hu)
  refine ⟨he, ?_⟩
  rw [triangularAdaptivePrime, he]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Under GRH, the least rejecting prime of an odd composite lies below the adaptive
pointwise cutoff. The new profile gives an actual witness and leastness transfers
its bound to the existing minimum. -/
theorem exists_least_triangularAdaptive {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ triangularAdaptiveSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_meanSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (30000000000 : ℝ) ≤ Real.log n
  · rw [triangularAdaptiveSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := triangularAdaptive_prime_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [triangularAdaptiveSelected, ite_eq_right hL]
    exact hb

/-- Under GRH, prime rounding preserves the adaptive cutoff for the least rejecting
prime of an odd composite. Apply the prime-rounding theorem to the least witness.
This gives the rounded pointwise envelope. -/
theorem exists_least_triangularAdaptivePrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ triangularAdaptivePrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_triangularAdaptive hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
