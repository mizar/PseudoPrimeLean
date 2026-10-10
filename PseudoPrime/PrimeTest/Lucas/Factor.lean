/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Params
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Lucas parameter factor detection

The executable check separates the possible gcd values for a prime modulus
from the stronger coprimality assumption used by Lucas-V prime theorems.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Boolean check that `gcd(|Q|, n)` is either trivial or the whole modulus.
For natural `n` and signed `Q`, accept when the gcd is `1` or `n`; reject a strict intermediate
factor. No primality hypothesis is part of the executable definition. The following lemmas
show prime acceptance and how a nontrivial proper gcd is detected.
-/
def qFactorCheck (n : ℕ) (Q : ℤ) : Bool :=
  Nat.gcd Q.natAbs n = 1 || Nat.gcd Q.natAbs n = n

/--
For prime `n`, the natural gcd of `|Q|` and `n` is `1` or `n`.
Only primality of the modulus is required; `Q` may be any signed integer, including zero.
The gcd divides `n`, so the divisor characterization of a prime proves the dichotomy.
This is the arithmetic justification for prime acceptance of `qFactorCheck`.
-/
theorem gcd_Q_eq_one_or_n_of_prime {n : ℕ} (hn : n.Prime) (Q : ℤ) :
    Nat.gcd Q.natAbs n = 1 ∨ Nat.gcd Q.natAbs n = n := by
  apply (Nat.dvd_prime hn).mp
  exact Nat.gcd_dvd_right Q.natAbs n

/--
A prime modulus is coprime to `|Q|` if their gcd is not the whole modulus.
Assume `n.Prime` and `gcd(|Q|, n) ≠ n`. The prime-gcd dichotomy leaves only gcd one,
which is exactly natural coprimality. This supplies a parameter coprimality premise when
Lucas results exclude the full-modulus gcd case separately.
-/
theorem q_coprime_of_prime_of_gcd_ne_n {n : ℕ} (hn : n.Prime) (Q : ℤ)
    (hnot : Nat.gcd Q.natAbs n ≠ n) : Nat.Coprime Q.natAbs n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases gcd_Q_eq_one_or_n_of_prime hn Q with hQ | hQ
  · exact hQ
  · exact False.elim (hnot hQ)

/--
Every prime modulus passes the gcd factor check for every signed `Q`.
The prime-gcd dichotomy gives one of the two accepted Boolean branches.
Simplifying that branch proves `qFactorCheck n Q = true`; no coprimality guard is necessary.
This ensures that proper-factor filtering cannot reject a prime input.
-/
theorem qFactorCheck_of_prime {n : ℕ} (hn : n.Prime) (Q : ℤ) : qFactorCheck n Q = true := by
  rcases gcd_Q_eq_one_or_n_of_prime hn Q with hQ | hQ
  · simp only [qFactorCheck, hQ, Bool.or_eq_true, decide_eq_true_eq, true_or]
  · simp only [qFactorCheck, hQ, Bool.or_eq_true, decide_eq_true_eq, or_true]

/--
A gcd strictly between one and the modulus makes `qFactorCheck n Q` false.
The strict lower and upper bounds exclude both accepted equalities.
The proof unfolds Boolean disjunction and uses the corresponding inequality-to-disequality
facts. This is a proper-factor rejection criterion, not a result about an exhausted search.
-/
theorem qFactorCheck_false_of_nontrivial {n : ℕ} {Q : ℤ} (h₁ : 1 < Nat.gcd Q.natAbs n)
    (h₂ : Nat.gcd Q.natAbs n < n) : qFactorCheck n Q = false := by
  simp only [qFactorCheck, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨ne_of_gt h₁, ne_of_lt h₂⟩

end PseudoPrime.PrimeTest
