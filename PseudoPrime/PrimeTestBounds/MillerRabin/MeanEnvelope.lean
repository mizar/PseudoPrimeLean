/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanAllFactors
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableCumulative

/-! # Pointwise and cumulative envelopes with the coefficient 427 / 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pointwise cutoff adds coefficient `427 / 1000` at logarithmic scale 80000.
Below that entrance it retains the previous factorial-selected bound. This combines the
new actual witness with every earlier candidate. -/
noncomputable def meanSelected (n : ℕ) : ℝ :=
  if (80000 : ℝ) ≤ Real.log n then min (factorialSelected n) ((427 / 1000 : ℝ) * (Real.log n) ^ 2)
  else factorialSelected n

/-- Prime rounding of `meanSelected` preserves every prime below the real cutoff.
It supplies the rounded version of the new pointwise envelope. -/
noncomputable def meanSelectedPrime (n : ℕ) : ℝ :=
  primeRound (meanSelected n)

/-- The mean-selected cutoff is at most the preceding factorial-selected cutoff.
The new branch takes a minimum and the other branch is unchanged. -/
theorem meanSelected_le (n : ℕ) : meanSelected n ≤ factorialSelected n := by
  by_cases h : (80000 : ℝ) ≤ Real.log n
  · rw [meanSelected, ite_eq_left h]
    exact min_le_left _ _
  · rw [meanSelected, ite_eq_right h]

/-- Below logarithmic scale 80000, the mean-selected cutoff equals the preceding cutoff.
This preserves the prior small-input choice. -/
theorem meanSelected_eq_of_log_lt {n : ℕ} (h : Real.log n < 80000) :
    meanSelected n = factorialSelected n := by exact ite_eq_right (not_le_of_gt h)

/-- On `2047 ≤ n < 3000`, the mean-selected cutoff remains three. The new branch is
inactive on this interval, so the preceding small-input result applies. -/
theorem meanSelected_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) : meanSelected n = 3 := by
  have h : Real.log n < 80000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  exact (meanSelected_eq_of_log_lt h).trans (factorialSelected_small_three hl hu)

/-- Prime rounding preserves the value three on `2047 ≤ n < 3000`. Apply the
pointwise small-interval equality and the prime-rounding identity at three. -/
theorem meanSelectedPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    meanSelectedPrime n = 3 := by
  rw [meanSelectedPrime, meanSelected_small_three hl hu]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Under GRH, the least rejecting prime for an odd composite is bounded by `meanSelected`.
Leastness transfers the new actual witness to the prior minimum. This supplies the
least-prime form of the pointwise envelope. -/
theorem exists_least_meanSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ meanSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_factorialSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (80000 : ℝ) ≤ Real.log n
  · rw [meanSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := prime_witness_427 hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [meanSelected, ite_eq_right hL]
    exact hb

/-- Under GRH, prime rounding preserves the mean-selected bound for the least rejecting
prime of an odd composite. Apply the prime-rounding comparison to the pointwise least
witness. This supplies the rounded public envelope. -/
theorem exists_least_meanSelectedPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ meanSelectedPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_meanSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

/-- The fixed-coefficient common-scale cap retains the paired history at the entrance and
uses `(427 / 1000) * L ^ 2` thereafter. It is valid as a cumulative cutoff even before
the new coefficient becomes applicable. -/
noncomputable def meanCumulativeCap (L : ℝ) : ℝ :=
  max (pairedCumulativeCap 80000) ((427 / 1000 : ℝ) * L ^ 2)

/-- Under GRH, `meanCumulativeCap L` bounds the least rejecting prime of every odd
composite with logarithm at most `L). Before the entrance use the paired history;
after it, transfer the fixed-coefficient witness to the common scale. -/
theorem leastPrime_le_meanScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ meanCumulativeCap L := by
  by_cases hhigh : (80000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := prime_witness_427 hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have hs := pow_le_pow_left₀ (by linarith only [hhigh] : 0 ≤ Real.log n) hlog 2
    exact
      ((Nat.cast_le.mpr hm).trans hb).trans
        ((mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 427 / 1000)).trans
          (le_max_right _ _))
  · have hprev := leastPrime_le_pairedScale hGRH hn ho hc 80000 (le_of_not_ge hhigh)
    exact hprev.trans (le_max_left _ _)

/-- The history-safe cumulative cutoff intersects the preceding cumulative envelope with
the fixed-coefficient cap. The cap retains the pre-entrance history. -/
noncomputable def meanCumulative (N : ℕ) : ℝ :=
  min (variableCumulative N) (meanCumulativeCap (Real.log N))

/-- Under GRH, the cumulative maximum of least rejecting primes is at most
`meanCumulative N`. Combine the earlier cumulative theorem with the new common-scale
bound. This is the history-safe counterpart of the pointwise improvement. -/
theorem cumulativeLeastPrime_le_mean (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (N : ℕ) : (cumulativeLeastPrime N : ℝ) ≤ meanCumulative N := by
  have hp0 : 0 ≤ pairedCumulativeCap 80000 :=
    (by norm_num only : (0 : ℝ) ≤ (4 / 9) * (70000 : ℝ) ^ 2).trans (le_max_left _ _)
  have hcap : ∀ L, 0 ≤ meanCumulativeCap L := fun L ↦ hp0.trans (le_max_left _ _)
  have h :=
    cumulativeLeastPrime_le_base meanCumulativeCap hcap
      (fun hn ho hc L hlog ↦ leastPrime_le_meanScale hGRH hn ho hc L hlog) [] hGRH N
  have h' : (cumulativeLeastPrime N : ℝ) ≤ meanCumulativeCap (Real.log N) := by
    simpa only [baseHistory] using h
  exact le_min (cumulativeLeastPrime_le_variable hGRH N) h'

end PseudoPrime.PrimeTestBounds.MillerRabin
