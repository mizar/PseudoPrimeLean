/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallPointwiseBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeCutoff

/-! # Pointwise and cumulative selections with the 0.28 bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Use the finite interval bound below 3000 and the global 0.28 maximum
bound otherwise. This preserves the verified small-input cutoff. -/
noncomputable def target028Selected (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n else max 2 ((7 / 25 : ℝ) * Real.log n ^ 2)

/-- The global 0.28 maximum cutoff at the natural endpoint `N`, used as
a cumulative bound for least rejecting primes. -/
noncomputable def target028Cumulative (N : ℕ) : ℝ :=
  max 2 ((7 / 25 : ℝ) * Real.log N ^ 2)

/-- Under GRH, the selection bounds the least rejecting prime for every odd
composite above one. Use the finite small-input certificate below 3000 and
the global 0.28 witness otherwise. -/
theorem target028Selected_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ target028Selected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases hN : n < 3000
  · obtain ⟨p, hp, hb, hr, hm⟩ := exists_least_smallInterval hn ho hc hN
    exact ⟨p, hp, hr, by simpa only [target028Selected, ite_eq_left hN] using hb, hm⟩
  · have hs := compositeLeastPrime_spec hGRH hn ho hc
    obtain ⟨q, hq, hqb, hqf⟩ := exists_prime_reject_028_global hGRH hn ho hc
    exact
      ⟨compositeLeastPrime n, hs.1, hs.2.1, by
        simpa only [target028Selected, ite_eq_right hN] using
          (Nat.cast_le.mpr (hs.2.2 q hq hqf)).trans hqb,
        hs.2.2⟩

/-- Under GRH, the cumulative least prime at every natural endpoint is
bounded by the global 0.28 maximum cutoff. -/
theorem cumulativeLeastPrime_le_target028
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ target028Cumulative N := by
  exact cumulativeLeastPrime_le_028 hGRH N

/-- Round the new pointwise cutoff down to the greatest prime it admits.
The selected least rejecting prime remains within this rounded cutoff. -/
noncomputable def target028Prime (n : ℕ) : ℝ :=
  primeRound (target028Selected n)

/-- Under GRH, prime rounding preserves the least rejecting prime and its
minimality for each odd composite above one. -/
theorem target028Prime_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ target028Prime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := target028Selected_least hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- The selected and rounded cutoffs both equal three on the interval from
2047 to 2999. The finite interval cutoff has this value, and prime rounding
preserves the prime three. -/
theorem target028_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    target028Selected n = 3 ∧ target028Prime n = 3 := by
  have he : target028Selected n = 3 := by
    rw [target028Selected, ite_eq_left hu, smallIntervalBound, ite_eq_right (not_lt.mpr hl)]
  constructor
  · exact he
  · change primeRound (target028Selected n) = 3
    rw [he]
    simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

end PseudoPrime.PrimeTestBounds.MillerRabin
