/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.Params
import Mathlib.Data.Nat.Prime.Basic

/-!
# Lucas parameter factor detection

The executable check separates the possible gcd values for a prime modulus
from the stronger coprimality assumption used by Lucas-V prime theorems.
-/

namespace PseudoPrime.PrimeTest

/-- Check that the gcd of a signed Lucas parameter and the modulus is trivial or total. -/
def qFactorCheck (n : ℕ) (Q : ℤ) : Bool :=
  Nat.gcd Q.natAbs n = 1 || Nat.gcd Q.natAbs n = n

/-- For a prime modulus, the gcd of `|Q|` and the modulus is `1` or the modulus. -/
theorem gcd_Q_eq_one_or_n_of_prime {n : ℕ} (hn : n.Prime) (Q : ℤ) :
    Nat.gcd Q.natAbs n = 1 ∨ Nat.gcd Q.natAbs n = n := by
  apply (Nat.dvd_prime hn).mp
  exact Nat.gcd_dvd_right Q.natAbs n

/-- A prime modulus is coprime to `|Q|` when the full-modulus gcd case is excluded. -/
theorem q_coprime_of_prime_of_gcd_ne_n {n : ℕ} (hn : n.Prime) (Q : ℤ)
    (hnot : Nat.gcd Q.natAbs n ≠ n) : Nat.Coprime Q.natAbs n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases gcd_Q_eq_one_or_n_of_prime hn Q with hQ | hQ
  · exact hQ
  · exact False.elim (hnot hQ)

/-- A prime modulus always passes the executable gcd factor check. -/
theorem qFactorCheck_of_prime {n : ℕ} (hn : n.Prime) (Q : ℤ) : qFactorCheck n Q = true := by
  rcases gcd_Q_eq_one_or_n_of_prime hn Q with hQ | hQ
  · simp only [qFactorCheck, hQ, Bool.or_eq_true, decide_eq_true_eq, true_or]
  · simp only [qFactorCheck, hQ, Bool.or_eq_true, decide_eq_true_eq, or_true]

/-- A gcd strictly between `1` and the modulus is detected as a factor. -/
theorem qFactorCheck_false_of_nontrivial {n : ℕ} {Q : ℤ} (h₁ : 1 < Nat.gcd Q.natAbs n)
    (h₂ : Nat.gcd Q.natAbs n < n) : qFactorCheck n Q = false := by
  simp only [qFactorCheck, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨ne_of_gt h₁, ne_of_lt h₂⟩

end PseudoPrime.PrimeTest
