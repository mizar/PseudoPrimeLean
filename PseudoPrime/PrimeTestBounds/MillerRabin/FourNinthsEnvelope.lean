/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextTunedIntervalSelection

/-! # Four-ninths selected and prime-rounded witness envelopes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Preserve the small interval cutoff and intersect the previous selected envelope
with four ninths of the squared logarithm at inputs at least 3000. -/
noncomputable def fourNinthsSelectedEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else min (nextTunedSelectedEnvelope n) ((4 / 9 : ℝ) * (Real.log n) ^ 2)

/-- Round the selected cutoff down to a prime while preserving any bounded prime. -/
noncomputable def fourNinthsPrimeEnvelope (n : ℕ) : ℝ :=
  primeRound (fourNinthsSelectedEnvelope n)

/-- The selected cutoff never exceeds the previous envelope. -/
theorem fourNinthsSelected_le_previous (n : ℕ) :
    fourNinthsSelectedEnvelope n ≤ nextTunedSelectedEnvelope n := by
  by_cases h : n < 3000
  · rw [fourNinthsSelectedEnvelope, ite_eq_left h, nextTunedSelectedEnvelope, ite_eq_left h]
  · rw [fourNinthsSelectedEnvelope, ite_eq_right h]
    exact min_le_left _ _

/-- Above the small branch the selected cutoff is at most the four-ninths bound. -/
theorem fourNinthsSelected_le_quad {n : ℕ} (h : 3000 ≤ n) :
    fourNinthsSelectedEnvelope n ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by
  rw [fourNinthsSelectedEnvelope, ite_eq_right (not_lt.mpr h)]
  exact min_le_right _ _

/-- Below 3000 the selected cutoff retains the prior small interval. -/
theorem fourNinthsSelected_small {n : ℕ} (h : n < 3000) :
    fourNinthsSelectedEnvelope n = smallIntervalBound n :=
  ite_eq_left h

/-- The selected cutoff remains three on the interval from 2047 to 3000. -/
theorem fourNinthsSelected_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    fourNinthsSelectedEnvelope n = 3 := by
  rw [fourNinthsSelected_small hu, smallIntervalBound, ite_eq_right (not_lt.mpr hl)]

/-- Prime rounding retains the value three on the same interval. -/
theorem fourNinthsPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    fourNinthsPrimeEnvelope n = 3 := by
  rw [fourNinthsPrimeEnvelope, fourNinthsSelected_small_three hl hu]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- The selected cutoff is monotone on the preserved interval. -/
theorem fourNinthsSelected_small_mono :
    MonotoneOn fourNinthsSelectedEnvelope (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [fourNinthsSelected_small_three hm.1 hm.2, fourNinthsSelected_small_three hn.1 hn.2]

/-- The prime-rounded cutoff is monotone on the preserved interval. -/
theorem fourNinthsPrime_small_mono : MonotoneOn fourNinthsPrimeEnvelope (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [fourNinthsPrime_small_three hm.1 hm.2, fourNinthsPrime_small_three hn.1 hn.2]

/-- Under GRH the least rejecting prime lies below the selected minimum.
Transfer the global four-ninths witness to the previous least witness by leastness. -/
theorem exists_least_fourNinthsSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ fourNinthsSelectedEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_nextTunedSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hN : n < 3000
  · rw [fourNinthsSelected_small hN]
    rw [nextTunedSelectedEnvelope, ite_eq_left hN] at hb
    exact hb
  · rw [fourNinthsSelectedEnvelope, ite_eq_right hN]
    apply le_min hb
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_witness_four_ninths hn ho hc hGRH
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb

/-- Under GRH prime rounding retains the least rejecting prime below the cutoff. -/
theorem exists_least_fourNinthsPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ fourNinthsPrimeEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_fourNinthsSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
