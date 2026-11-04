/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveCumulative

/-! # Pointwise adaptive Gaussian envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The selected cutoff adds the adaptive Gaussian candidate at its entrance. -/
noncomputable def gaussianAdaptiveSelected (n : ℕ) : ℝ :=
  if (2000000000000 : ℝ) ≤ Real.log n then
    min (triangularAdaptiveSelected n)
      (((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * (Real.log n) ^ 2)
  else triangularAdaptiveSelected n

/-- Prime rounding of the Gaussian-selected cutoff preserves prime witnesses. -/
noncomputable def gaussianAdaptivePrime (n : ℕ) : ℝ :=
  primeRound (gaussianAdaptiveSelected n)

/-- The Gaussian-selected cutoff is at most the preceding triangular cutoff. -/
theorem gaussianAdaptiveSelected_le (n : ℕ) :
    gaussianAdaptiveSelected n ≤ triangularAdaptiveSelected n := by
  by_cases h : (2000000000000 : ℝ) ≤ Real.log n
  · rw [gaussianAdaptiveSelected, ite_eq_left h]
    exact min_le_left _ _
  · rw [gaussianAdaptiveSelected, ite_eq_right h]

/-- Before the Gaussian entrance the preceding cutoff is unchanged. -/
theorem gaussianAdaptiveSelected_eq {n : ℕ} (h : Real.log n < 2000000000000) :
    gaussianAdaptiveSelected n = triangularAdaptiveSelected n := by
  exact ite_eq_right (not_le_of_gt h)

/-- The Gaussian-selected and rounded cutoffs remain three on the small interval. -/
theorem gaussianAdaptive_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    gaussianAdaptiveSelected n = 3 ∧ gaussianAdaptivePrime n = 3 := by
  have h : Real.log n < 2000000000000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have he : gaussianAdaptiveSelected n = 3 :=
    (gaussianAdaptiveSelected_eq h).trans (triangularAdaptive_small_three hl hu).1
  refine ⟨he, ?_⟩
  rw [gaussianAdaptivePrime, he]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Under GRH, the Gaussian-selected cutoff bounds the least rejecting prime of an odd composite. -/
theorem exists_least_gaussianAdaptive {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussianAdaptiveSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_triangularAdaptive hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (2000000000000 : ℝ) ≤ Real.log n
  · rw [gaussianAdaptiveSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := gaussianAdaptive_prime_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [gaussianAdaptiveSelected, ite_eq_right hL]
    exact hb

/-- Under GRH, prime rounding preserves the least rejecting prime for an odd composite. -/
theorem exists_least_gaussianAdaptivePrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussianAdaptivePrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_gaussianAdaptive hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
