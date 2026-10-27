/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MidscaleIntervalSelection
/-! # Pointwise small-input witness bound -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pointwise small-input cutoff: three at 2047 and two otherwise. It is not a cumulative
bound. -/
def smallPointwiseBound (n : ℕ) : ℝ := if n = 2047 then 3 else 2

/-- Every odd composite 1<n<3000 has a prime rejecting MR within the pointwise cutoff. Reuse the
existing finite classification and the 2047 exception; no GRH or new enumeration is used. -/
theorem exists_prime_smallPointwise {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hN : n < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ smallPointwiseBound n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases he : n = 2047
  · simpa only [smallPointwiseBound, ite_eq_left he] using
      exists_prime_small_three hn ho hc hN
  · have hr := PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp
      (PrimeTest.base_two_rejects_of_lt_3000_of_ne_2047 hn ho hc hN he)
    refine ⟨2, Nat.prime_two, ?_, hr⟩
    simp only [smallPointwiseBound, ite_eq_right he, Nat.cast_ofNat, le_refl]

/-- Every odd composite 1<n<3000 has a least rejecting prime within the pointwise cutoff. Apply
least-prime extraction to the actual witness theorem; no GRH is required. -/
theorem exists_least_smallPointwise {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hN : n < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ smallPointwiseBound n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_smallPointwise hn ho hc hN)

/-- The small interval cutoff: two below 2047 and three from 2047 onward.
The public envelope uses this uniform value on 2047<=n<3000 to match its interval table. -/
def smallIntervalBound (n : ℕ) : ℝ := if n < 2047 then 2 else 3

/-- Every odd composite 1<n<3000 has an actual rejecting prime within the interval
cutoff. Reuse the base-two classification below 2047 and the two-or-three bound above it. -/
theorem exists_prime_smallInterval {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hN : n < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ smallIntervalBound n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  dsimp only [smallIntervalBound]
  by_cases h : n < 2047
  · rw [ite_eq_left h]
    simpa only [smallPointwiseBound, ite_eq_right (ne_of_lt h)] using
      exists_prime_smallPointwise hn ho hc hN
  · rw [ite_eq_right h]
    exact exists_prime_small_three hn ho hc hN

/-- Every odd composite 1<n<3000 has a least rejecting prime within the interval
cutoff. Extract the least prime from the actual witness; no GRH is required. -/
theorem exists_least_smallInterval {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hN : n < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ smallIntervalBound n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject
    (exists_prime_smallInterval hn ho hc hN)

end PseudoPrime.PrimeTestBounds.MillerRabin
