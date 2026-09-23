/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.MillerRabinBoundGrh.Definition
import PseudoPrime.PrimeTest.MillerRabin.Computation.SmallLogBound

/-!
# Small-input branch for the GRH Miller–Rabin witness bound
-/

namespace PseudoPrime.MillerRabinBoundGrh

/--
For odd composite `n < 3000`, the finite base-`2`/`3` classification supplies a prime witness.
The logarithmic estimate is unconditional, and the arbitrary odd decomposition is transferred
through the Strong Miller–Rabin specification.
-/
theorem exists_prime_millerRabin_witness_le_log_sq_of_lt_3000 {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d)
    (hlt : n < 3000) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n) := by
  exact PrimeTest.exists_prime_millerRabin_witness_le_log_sq_of_lt_3000
    hn hnOdd hnNotPrime hdecomp hdOdd hlt

end PseudoPrime.MillerRabinBoundGrh
