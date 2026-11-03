/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowEnvelope

/-! # Further high-window Miller–Rabin witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Intersect the existing high-window cutoff with the strongest applicable later profile.
The guards are ordered by entrance and the coefficients decrease at each entrance.
Below 120 billion the original high-window cutoff is returned unchanged. -/
noncomputable def highWindowExtended (n : ℕ) : ℝ :=
  if (600000000000 : ℝ) ≤ Real.log n then
    min (highWindowSelected n) ((36 / 125 : ℝ) * Real.log n ^ 2)
  else
    if (300000000000 : ℝ) ≤ Real.log n then
      min (highWindowSelected n) ((37 / 125 : ℝ) * Real.log n ^ 2)
    else
      if (120000000000 : ℝ) ≤ Real.log n then
        min (highWindowSelected n) ((323 / 1000 : ℝ) * Real.log n ^ 2)
      else highWindowSelected n

/-- Prime rounding retains every prime bounded by the extended selected cutoff. -/
noncomputable def highWindowExtendedPrime (n : ℕ) : ℝ :=
  primeRound (highWindowExtended n)

/-- The extended cutoff never exceeds the previously selected cutoff. -/
theorem highWindowExtended_le (n : ℕ) : highWindowExtended n ≤ highWindowSelected n := by
  by_cases h600 : (600000000000 : ℝ) ≤ Real.log n
  · rw [highWindowExtended, ite_eq_left h600]
    exact min_le_left _ _
  · rw [highWindowExtended, ite_eq_right h600]
    by_cases h300 : (300000000000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left h300]
      exact min_le_left _ _
    · rw [ite_eq_right h300]
      by_cases h120 : (120000000000 : ℝ) ≤ Real.log n
      · rw [ite_eq_left h120]
        exact min_le_left _ _
      · rw [ite_eq_right h120]

/-- Prime rounding preserves the pointwise comparison with the previous rounded cutoff. -/
theorem highWindowExtendedPrime_le (n : ℕ) : highWindowExtendedPrime n ≤ highWindowPrime n :=
  primeRound_mono (highWindowExtended_le n)

/-- The extended cutoff agrees with the previous one before logarithmic scale 120 billion. -/
theorem highWindowExtended_eq_of_log_lt {n : ℕ} (h : Real.log n < 120000000000) :
    highWindowExtended n = highWindowSelected n := by
  have h300 : ¬(300000000000 : ℝ) ≤ Real.log n := not_le_of_gt (lt_of_lt_of_le h (by norm_num only))
  have h600 : ¬(600000000000 : ℝ) ≤ Real.log n := not_le_of_gt (lt_of_lt_of_le h (by norm_num only))
  rw [highWindowExtended, ite_eq_right h600, ite_eq_right h300, ite_eq_right (not_le_of_gt h)]

/-- The extended selected cutoff remains three on the preserved small interval. -/
theorem highWindowExtended_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    highWindowExtended n = 3 := by
  have h : Real.log n < 120000000000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  exact (highWindowExtended_eq_of_log_lt h).trans (highWindowSelected_small_three hl hu)

/-- The extended rounded cutoff remains three on the preserved small interval. -/
theorem highWindowExtendedPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    highWindowExtendedPrime n = 3 := by
  rw [highWindowExtendedPrime, highWindowExtended_small_three hl hu]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- The extended selected cutoff is monotone on the preserved constant-three interval. -/
theorem highWindowExtended_small_mono : MonotoneOn highWindowExtended (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [highWindowExtended_small_three hm.1 hm.2, highWindowExtended_small_three hn.1 hn.2]

/-- The extended rounded cutoff is monotone on the preserved constant-three interval. -/
theorem highWindowExtendedPrime_small_mono :
    MonotoneOn highWindowExtendedPrime (Set.Ico 2047 3000) := by
  intro m hm n hn _
  rw [highWindowExtendedPrime_small_three hm.1 hm.2, highWindowExtendedPrime_small_three hn.1 hn.2]

/-- Under GRH, the least rejecting prime is bounded by the extended selected cutoff.
Each active candidate supplies a rejecting prime and leastness transfers its bound. -/
theorem exists_least_highWindowExtended {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ highWindowExtended n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_highWindowSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases h600 : (600000000000 : ℝ) ≤ Real.log n
  · rw [highWindowExtended, ite_eq_left h600]
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP0288 hn ho hc hGRH h600
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [highWindowExtended, ite_eq_right h600]
    by_cases h300 : (300000000000 : ℝ) ≤ Real.log n
    · rw [ite_eq_left h300]
      obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP0296 hn ho hc hGRH h300
      exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
    · rw [ite_eq_right h300]
      by_cases h120 : (120000000000 : ℝ) ≤ Real.log n
      · rw [ite_eq_left h120]
        obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_highWindowP0323 hn ho hc hGRH h120
        exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
      · rw [ite_eq_right h120]
        exact hb

/-- Under GRH, prime rounding still bounds the least rejecting prime. -/
theorem exists_least_highWindowExtendedPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ highWindowExtendedPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_highWindowExtended hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
