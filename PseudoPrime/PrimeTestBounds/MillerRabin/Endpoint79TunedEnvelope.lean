/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPrime79Plus

/-! # Guarded fixed-79 improvement preserving the small MR interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the tuned selected cutoff with 79 only at inputs at least 3000
whose logarithm is at most the certified fixed-79 cap. This adds a finite
candidate while preserving all small-input values and the existing baseline. -/
noncomputable def endpoint79Selected (n : ℕ) : ℝ :=
  if 3000 ≤ n ∧ Real.log n ≤ LLS.PaperStatements.prime79PlusCap then
    min (tunedSelectedEnvelope n) 79
  else tunedSelectedEnvelope n

/-- Round the guarded fixed-79 selected cutoff to the greatest permitted prime.
The input is the tested integer. Prime witnesses under the selected bound
remain under this bound, which feeds the public rounded cutoff API. -/
noncomputable def endpoint79Prime (n : ℕ) : ℝ :=
  primeRound (endpoint79Selected n)

/-- For every input, adjoining the certified fixed-79 branch cannot increase
the tuned selected cutoff. Inspect its guard and use the minimum bound. -/
theorem endpoint79Selected_le_tuned (n : ℕ) : endpoint79Selected n ≤ tunedSelectedEnvelope n := by
  by_cases h : 3000 ≤ n ∧ Real.log n ≤ LLS.PaperStatements.prime79PlusCap
  · rw [endpoint79Selected, ite_eq_left h]
    exact min_le_left _ _
  · rw [endpoint79Selected, ite_eq_right h]

/-- Every input in [2047,3000) retains selected cutoff three. The new guard
is inactive there, so use the existing exact small-interval theorem. -/
theorem endpoint79Selected_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    endpoint79Selected n = 3 := by
  have hg : ¬(3000 ≤ n ∧ Real.log n ≤ LLS.PaperStatements.prime79PlusCap) := fun h ↦
    (not_le.mpr hU) h.1
  rw [endpoint79Selected, ite_eq_right hg, tunedSelected_small_three hN hU]

/-- Prime rounding preserves cutoff three on [2047,3000), including 2047.
Rewrite the selected cutoff and use exact rounding of the prime three. -/
theorem endpoint79Prime_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    endpoint79Prime n = 3 := by
  rw [endpoint79Prime, endpoint79Selected_small_three hN hU]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- The guarded selected cutoff is nondecreasing on [2047,3000). Both
values are exactly three, so the proof requires no interval sampling. -/
theorem endpoint79Selected_small_mono : MonotoneOn endpoint79Selected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [endpoint79Selected_small_three hm.1 hm.2, endpoint79Selected_small_three hn.1 hn.2]

/-- On the certified logarithmic improvement interval, the guarded selection
is exactly 79. The old complete tuned cutoff is strictly larger there. -/
theorem endpoint79Selected_eq_79 {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1265 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) : endpoint79Selected n = 79 := by
  have hb := (endpoint79Plus_strict hn hN hL hU).1
  rw [endpoint79Selected, ite_eq_left ⟨hN, hU⟩, min_eq_right hb.le]

/-- On the fixed-79 improvement interval, the rounded cutoff is also exactly
79. Rewrite the selected value and round the certified prime 79. -/
theorem endpoint79Prime_eq_79 {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1265 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) : endpoint79Prime n = 79 := by
  rw [endpoint79Prime, endpoint79Selected_eq_79 hn hN hL hU]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 79)

/-- The guarded selected and rounded cutoffs strictly improve the corresponding
complete tuned public values on the certified interval. Use both exact 79
identities and the fixed-79 strict comparison; no decimal evaluation is used. -/
theorem endpoint79Guard_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1265 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) :
    endpoint79Selected n < tunedSelectedEnvelope n ∧ endpoint79Prime n < tunedPrimeEnvelope n := by
  rw [endpoint79Selected_eq_79 hn hN hL hU, endpoint79Prime_eq_79 hn hN hL hU]
  exact endpoint79Plus_strict hn hN hL hU

/-- Under GRH, every odd composite above one has an actual least rejecting
prime under the guarded selected cutoff. Reuse the old least prime and bound
it by the new fixed-79 witness whenever the guard is active. The witness domain
and the least-prime property are unchanged. -/
theorem exists_least_endpoint79Selected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ endpoint79Selected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_tunedSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases h : 3000 ≤ n ∧ Real.log n ≤ LLS.PaperStatements.prime79PlusCap
  · rw [endpoint79Selected, ite_eq_left h]
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_endpoint79Plus hn ho hc hGRH h.2
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [endpoint79Selected, ite_eq_right h]
    exact hb

/-- Under GRH, the same least rejecting prime lies under the rounded
fixed-79 cutoff. Prime-preserving rounding transfers the selected witness. -/
theorem exists_least_endpoint79Prime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ endpoint79Prime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_endpoint79Selected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- Under GRH, an odd composite above one has an actual rejecting prime
under the guarded selected cutoff. Forget only the least-prime property. -/
theorem exists_prime_endpoint79Selected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ endpoint79Selected n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_endpoint79Selected hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- Under GRH, an odd composite above one has an actual rejecting prime
under the rounded fixed-79 cutoff. Forget only the least-prime property. -/
theorem exists_prime_endpoint79Prime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ endpoint79Prime n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_endpoint79Prime hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- Inputs below 2047 retain selected cutoff two. The new guard cannot be
active below 3000, so use the existing tuned small-input identity. -/
theorem endpoint79Selected_small_two {n : ℕ} (hN : n < 2047) : endpoint79Selected n = 2 := by
  have hU := hN.trans (by norm_num only : 2047 < 3000)
  have hg : ¬(3000 ≤ n ∧ Real.log n ≤ LLS.PaperStatements.prime79PlusCap) := fun h ↦
    (not_le.mpr hU) h.1
  rw [endpoint79Selected, ite_eq_right hg, tunedSelected_small_two hN]

/-- Inputs below 2047 retain rounded cutoff two. Rewrite the selected value
and use exact rounding of the prime two. -/
theorem endpoint79Prime_small_two {n : ℕ} (hN : n < 2047) : endpoint79Prime n = 2 := by
  rw [endpoint79Prime, endpoint79Selected_small_two hN]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 2)

/-- The rounded cutoff is nondecreasing on [2047,3000), since every value
on that interval is exactly three. This also includes the boundary 2047. -/
theorem endpoint79Prime_small_mono : MonotoneOn endpoint79Prime (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [endpoint79Prime_small_three hm.1 hm.2, endpoint79Prime_small_three hn.1 hn.2]

/-- At every input above one, the guarded rounded cutoff is no larger than
the complete tuned rounded cutoff. Use monotonicity of prime rounding and
the existing equality between tuned witness and selected expressions. -/
theorem endpoint79Prime_le_tuned {n : ℕ} (hn : 1 < n) :
    endpoint79Prime n ≤ tunedPrimeEnvelope n := by
  rw [endpoint79Prime, tunedPrimeEnvelope, tuned_eq_selected hn]
  exact primeRound_mono (endpoint79Selected_le_tuned n)

end PseudoPrime.PrimeTestBounds.MillerRabin
