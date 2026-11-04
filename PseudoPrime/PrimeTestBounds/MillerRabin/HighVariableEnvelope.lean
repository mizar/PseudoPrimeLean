/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowExtended

/-! # Pointwise paired-coefficient Miller–Rabin envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The high-range paired-coefficient witness bound for a natural input `n`. For odd composite
inputs with `log n ≥ 70000`, GRH supplies a rejecting prime below this cutoff. -/
noncomputable def pairedWitnessBound (n : ℕ) : ℝ :=
  (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2

/-- Intersect the previous real cutoff with the paired bound from logarithmic scale `70000`.
Below that entrance the previous cutoff is retained, including its small-input behavior. -/
noncomputable def pairedSelected (n : ℕ) : ℝ :=
  if (70000 : ℝ) ≤ Real.log n then min (highWindowExtended n) (pairedWitnessBound n)
  else highWindowExtended n

/-- Round the selected paired cutoff down to a prime, retaining every prime witness within the
real cutoff. This is the prime-rounded counterpart of `pairedSelected`. -/
noncomputable def pairedSelectedPrime (n : ℕ) : ℝ :=
  primeRound (pairedSelected n)

/-- The paired selected cutoff never exceeds the prior extended cutoff. The high-range branch
is a minimum and the low-range branch is unchanged. -/
theorem pairedSelected_le (n : ℕ) : pairedSelected n ≤ highWindowExtended n := by
  by_cases h : (70000 : ℝ) ≤ Real.log n
  · rw [pairedSelected, ite_eq_left h]
    exact min_le_left _ _
  · rw [pairedSelected, ite_eq_right h]

/-- The rounded paired cutoff is bounded by the previous rounded cutoff because prime rounding
is monotone. -/
theorem pairedSelectedPrime_le (n : ℕ) : pairedSelectedPrime n ≤ highWindowExtendedPrime n := by
  exact primeRound_mono (pairedSelected_le n)

/-- Below the high-range entrance, the paired cutoff agrees with the previous extended cutoff. -/
theorem pairedSelected_eq_of_log_lt {n : ℕ} (h : Real.log n < 70000) :
    pairedSelected n = highWindowExtended n := by exact ite_eq_right (not_le_of_gt h)

/-- On `2047 ≤ n < 3000`, the selected paired cutoff remains three. The high-range entrance is
not reached on this preserved small interval. -/
theorem pairedSelected_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    pairedSelected n = 3 := by
  have h : Real.log n < 70000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  exact (pairedSelected_eq_of_log_lt h).trans (highWindowExtended_small_three hl hu)

/-- On the same preserved small interval, the prime-rounded paired cutoff also remains three. -/
theorem pairedSelectedPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    pairedSelectedPrime n = 3 := by
  rw [pairedSelectedPrime, pairedSelected_small_three hl hu]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Under GRH, the least rejecting prime for an odd composite lies below the new selected
cutoff. Above the entrance, leastness transfers the paired witness to the previous minimum. -/
theorem exists_least_pairedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ pairedSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_highWindowExtended hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (70000 : ℝ) ≤ Real.log n
  · rw [pairedSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := paired_prime_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [pairedSelected, ite_eq_right hL]
    exact hb

/-- Under GRH, prime rounding preserves the selected upper bound for the least rejecting prime. -/
theorem exists_least_pairedSelectedPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ pairedSelectedPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_pairedSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
