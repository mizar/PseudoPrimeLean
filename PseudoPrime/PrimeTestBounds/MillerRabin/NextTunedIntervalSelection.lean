/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.NextTunedWitnessEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPrime79Plus
public import PseudoPrime.PrimeTestBounds.MillerRabin.SeededSurplusComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.Endpoint79TunedEnvelope

/-! # Exact small values and strict improvement of the next tuned envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every natural input below 2047 retains selected value two without GRH or parity assumptions. -/
theorem nextTunedSelected_small_two {n : ℕ} (hN : n < 2047) : nextTunedSelectedEnvelope n = 2 := by
  rw [nextTunedSelectedEnvelope, ite_eq_left (hN.trans (by norm_num only : 2047 < 3000)),
    smallIntervalBound, ite_eq_left hN]

/-- Every natural input in [2047,3000) retains selected value exactly three. -/
theorem nextTunedSelected_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    nextTunedSelectedEnvelope n = 3 := by
  rw [nextTunedSelectedEnvelope, ite_eq_left hU, smallIntervalBound, ite_eq_right (not_lt.mpr hN)]

/-- Prime rounding preserves value two for every input below 2047. -/
theorem nextTunedPrime_small_two {n : ℕ} (hN : n < 2047) : nextTunedPrimeEnvelope n = 2 := by
  rw [nextTunedPrimeEnvelope, nextTuned_eq_small (hN.trans (by norm_num only : 2047 < 3000)),
    smallIntervalBound, ite_eq_left hN]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 2)

/-- Prime rounding preserves value three on the exact finite interval [2047,3000). -/
theorem nextTunedPrime_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    nextTunedPrimeEnvelope n = 3 := by
  rw [nextTunedPrimeEnvelope, nextTuned_eq_small hU, smallIntervalBound,
    ite_eq_right (not_lt.mpr hN)]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- The fixed-79 extension strictly improves both full tuned values on [12.65,12.659]. -/
theorem nextTuned79_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1265 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ LLS.PaperStatements.prime79PlusCap) :
    nextTunedSelectedEnvelope n < tunedSelectedEnvelope n ∧
      nextTunedPrimeEnvelope n < tunedPrimeEnvelope n := by
  have hb := nextTuned_le79 hN hU
  have hs := endpoint79Plus_strict hn hN hL hU
  exact
    ⟨(by
        rw [← nextTuned_eq_selected hn]; exact hb.trans_lt hs.1),
      (primeRound_le _).trans_lt (hb.trans_lt hs.2)⟩

/-- The public new selection strictly improves full tuned on the closed band [245,255]. -/
theorem nextTunedSeed35_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 245 ≤ Real.log n)
    (hU : Real.log n ≤ 255) : nextTunedSelectedEnvelope n < tunedSelectedEnvelope n := by
  rw [← nextTuned_eq_selected hn]
  exact
    (nextTuned_le_seeded false (by linarith only [hL])).trans_lt (seededSurplus35_lt_tuned hN hL hU)

/-- The public new selection strictly improves full tuned
from scale 300 to the first high entrance. -/
theorem nextTunedSeed50_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 300 ≤ Real.log n)
    (hU : Real.log n < 30000000000) : nextTunedSelectedEnvelope n < tunedSelectedEnvelope n := by
  rw [← nextTuned_eq_selected hn]
  exact
    (nextTuned_le_seeded true (by linarith only [hL])).trans_lt (seededSurplus50_lt_tuned hN hL hU)

/-- The combined next-tuned selected cutoff is nondecreasing on [2047,3000).
Use its exact value three at both endpoints, including the boundary 2047. -/
theorem nextTunedSelected_small_mono :
    MonotoneOn nextTunedSelectedEnvelope (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [nextTunedSelected_small_three hm.1 hm.2,
    nextTunedSelected_small_three hn.1 hn.2]

/-- The combined rounded cutoff is nondecreasing on [2047,3000). Its exact
constant-three theorem proves the whole interval without finite sampling. -/
theorem nextTunedPrime_small_mono : MonotoneOn nextTunedPrimeEnvelope (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [nextTunedPrime_small_three hm.1 hm.2, nextTunedPrime_small_three hn.1 hn.2]

/-- At every input above one, adding the Gaussian surplus candidates cannot
increase the independently exported fixed-79 selected cutoff. Compare with
both old tuned and fixed-79 bounds whenever the latter guard is active. -/
theorem nextTunedSelected_le_endpoint79 {n : ℕ} (hn : 1 < n) :
    nextTunedSelectedEnvelope n ≤ endpoint79Selected n := by
  by_cases h : 3000 ≤ n ∧ Real.log n ≤ LLS.PaperStatements.prime79PlusCap
  · rw [endpoint79Selected, ite_eq_left h]
    apply le_min (nextTunedSelected_le_tuned hn)
    rw [← nextTuned_eq_selected hn]
    exact nextTuned_le79 h.1 h.2
  · rw [endpoint79Selected, ite_eq_right h]
    exact nextTunedSelected_le_tuned hn

/-- Prime rounding preserves domination of the independent fixed-79 API by
the full next-tuned envelope at every input above one. -/
theorem nextTunedPrime_le_endpoint79 {n : ℕ} (hn : 1 < n) :
    nextTunedPrimeEnvelope n ≤ endpoint79Prime n := by
  rw [nextTunedPrimeEnvelope, endpoint79Prime, nextTuned_eq_selected hn]
  exact primeRound_mono (nextTunedSelected_le_endpoint79 hn)


end PseudoPrime.PrimeTestBounds.MillerRabin
