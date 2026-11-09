/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Computation.Small

/-! # Finite small-input rejecting-prime witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite 1<n<3000, one of the primes two and three rejects strong MR.
Transfer the existing Boolean rejection certificate to the canonical pass predicate.
This theorem needs no GRH and is used only in the finite base. -/
theorem exists_prime_small_three {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (hN : n < 3000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 3 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases PrimeTest.base_two_or_three_rejects_of_lt_3000 hn ho hc hN with h2 | h3
  · exact
      ⟨2, Nat.prime_two, by norm_num only,
        PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp h2⟩
  · exact
      ⟨3, Nat.prime_three, by norm_num only,
        PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp h3⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
