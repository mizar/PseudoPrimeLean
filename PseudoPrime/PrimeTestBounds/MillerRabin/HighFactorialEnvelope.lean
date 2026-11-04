/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableEnvelope

/-! # Pointwise factorial-coefficient Miller–Rabin envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The factorial-coefficient witness bound for a natural input `n`. Under GRH, it bounds a
rejecting prime for every odd composite with `log n ≥ 80000`. -/
noncomputable def factorialWitnessBound (n : ℕ) : ℝ :=
  (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2

/-- Intersect the paired cutoff with the factorial cutoff from logarithmic scale `80000`. Below
that entrance the paired cutoff is retained, including its small-input behavior. -/
noncomputable def factorialSelected (n : ℕ) : ℝ :=
  if (80000 : ℝ) ≤ Real.log n then min (pairedSelected n) (factorialWitnessBound n)
  else pairedSelected n

/-- Prime rounding of the factorial-selected cutoff retains every prime below the real cutoff. -/
noncomputable def factorialSelectedPrime (n : ℕ) : ℝ :=
  primeRound (factorialSelected n)

/-- The factorial selected cutoff is at most the preceding paired cutoff. -/
theorem factorialSelected_le (n : ℕ) : factorialSelected n ≤ pairedSelected n := by
  by_cases h : (80000 : ℝ) ≤ Real.log n
  · rw [factorialSelected, ite_eq_left h]
    exact min_le_left _ _
  · rw [factorialSelected, ite_eq_right h]

/-- Prime rounding preserves comparison with the preceding paired cutoff. -/
theorem factorialSelectedPrime_le (n : ℕ) : factorialSelectedPrime n ≤ pairedSelectedPrime n := by
  exact primeRound_mono (factorialSelected_le n)

/-- Below logarithmic scale `80000`, the factorial-selected cutoff equals the paired cutoff. -/
theorem factorialSelected_eq_of_log_lt {n : ℕ} (h : Real.log n < 80000) :
    factorialSelected n = pairedSelected n := by exact ite_eq_right (not_le_of_gt h)

/-- The factorial-selected cutoff remains three for `2047 ≤ n < 3000`. -/
theorem factorialSelected_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    factorialSelected n = 3 := by
  have h : Real.log n < 80000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  exact (factorialSelected_eq_of_log_lt h).trans (pairedSelected_small_three hl hu)

/-- Prime rounding also preserves the cutoff three on the same small interval. -/
theorem factorialSelectedPrime_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    factorialSelectedPrime n = 3 := by
  rw [factorialSelectedPrime, factorialSelected_small_three hl hu]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Under GRH, the least rejecting prime for an odd composite lies below the factorial-selected
cutoff. Above its entrance, leastness transfers the factorial witness to the previous minimum. -/
theorem exists_least_factorialSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ factorialSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_pairedSelected hn ho hc hGRH
  refine ⟨p, hp, hr, ?_, hm⟩
  by_cases hL : (80000 : ℝ) ≤ Real.log n
  · rw [factorialSelected, ite_eq_left hL]
    obtain ⟨q, hq, hqb, hqr⟩ := factorial_prime_witness hn ho hc hGRH hL
    exact le_min hb ((Nat.cast_le.mpr (hm q hq hqr)).trans hqb)
  · rw [factorialSelected, ite_eq_right hL]
    exact hb

/-- Under GRH, prime rounding preserves the factorial-selected bound for the least rejecting
prime. The proof applies the prime-rounding comparison to the least-prime witness. -/
theorem exists_least_factorialSelectedPrime {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ factorialSelectedPrime n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_factorialSelected hn ho hc hGRH
  exact ⟨p, hp, hr, prime_le_primeRound hp hb, hm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
