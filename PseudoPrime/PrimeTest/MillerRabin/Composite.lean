/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-!
# Prime-factor cases for composite moduli
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Every composite natural modulus greater than one has a prime-square divisor or two distinct prime
divisors whose product divides it. This elementary split selects the appropriate subgroup
construction below and does not assume that `n` is squarefree.
-/
theorem prime_square_or_distinct_primes_dvd {n : ℕ} (hn : 1 < n) (hnComposite : ¬Nat.Prime n) :
    (∃ q : ℕ, Nat.Prime q ∧ q ^ 2 ∣ n) ∨
      (∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ q ≠ r ∧ q * r ∣ n) := by
  have hnNeOne : n ≠ 1 := Nat.ne_of_gt hn
  obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hnNeOne
  obtain ⟨m, rfl⟩ := hqdiv
  by_cases hqm : q ∣ m
  · refine Or.inl ⟨q, hq, ?_⟩
    rw [pow_two]
    exact Nat.mul_dvd_mul_left q hqm
  · have hmNeOne : m ≠ 1 := by
      intro hm
      apply hnComposite
      rw [hm, Nat.mul_one]
      exact hq
    obtain ⟨r, hr, hrdiv⟩ := Nat.exists_prime_and_dvd hmNeOne
    apply Or.inr
    refine ⟨q, r, hq, hr, ?_, ?_⟩
    · intro hqr
      apply hqm
      rw [hqr]
      exact hrdiv
    · exact Nat.mul_dvd_mul_left q hrdiv

/-- An odd modulus has no even prime divisor; used for each factor in the two subgroup branches. -/
private theorem odd_prime_factor_ne_two {n q : ℕ} (hnOdd : Odd n) (hq : Nat.Prime q)
    (hqdiv : q ∣ n) : q ≠ 2 := by
  intro hqEq
  subst q
  exact (Nat.not_even_iff_odd.mpr hnOdd) (even_iff_two_dvd.mpr hqdiv)

/-- For odd composite `n > 1`, some proper subgroup of `(ZMod n)ˣ` contains a unit
representative of every canonical strong-test pass. If a prime square divides `n`, use
`fermatSubgroup`; otherwise two distinct prime divisors give a proper `signSubgroup`.
This is the subgroup interface consumed by witness bounds. -/
theorem exists_proper_subgroup_containing_strongMillerRabinPass {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬Nat.Prime n) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H ≠ ⊤ ∧
        ∀ x : ZMod n, StrongMillerRabinPass n x → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = x := by
  rcases prime_square_or_distinct_primes_dvd hn hnComposite with hsquare | hdifferent
  · obtain ⟨q, hq, hq2div⟩ := hsquare
    have hqdiv : q ∣ n := dvd_trans (by exact ⟨q, by rw [pow_two]⟩) hq2div
    have hq2 := odd_prime_factor_ne_two hnOdd hq hqdiv
    refine ⟨fermatSubgroup n, fermatSubgroup_ne_top_of_prime_square_dvd hn hq hq2 hq2div, ?_⟩
    intro x hpass
    exact strongMillerRabinPass_mem_fermatSubgroup hn hnOdd hpass
  · obtain ⟨q, r, hq, hr, hqr, hdiv⟩ := hdifferent
    have hqdiv : q ∣ n := dvd_trans ⟨r, rfl⟩ hdiv
    have hq2 := odd_prime_factor_ne_two hnOdd hq hqdiv
    let H := signSubgroup n (2 ^ (padicValNat 2 (q - 1) - 1) * Nat.divMaxPow (n - 1) 2)
    refine ⟨H, signSubgroup_ne_top_of_distinct_prime_dvd hn hnOdd hq hr hqr hdiv, ?_⟩
    intro x hpass
    exact strongMillerRabinPass_mem_signSubgroup hn hnOdd hpass hq (hq.odd_of_ne_two hq2) hqdiv

/--
For modulus 9, the Fermat subgroup is proper because the odd prime square 3²
divides it. Instantiate the prime-square theorem and verify the numerical premises by
normalization; this exercises the square-factor subgroup branch.
-/
example : fermatSubgroup 9 ≠ ⊤ := by
  exact
    fermatSubgroup_ne_top_of_prime_square_dvd (n := 9) (q := 3) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)

/--
For modulus 25, the Fermat subgroup is proper because the odd prime square 5²
divides it. Instantiate the prime-square theorem and verify the numerical premises by
normalization; this exercises the square-factor subgroup branch.
-/
example : fermatSubgroup 25 ≠ ⊤ := by
  exact
    fermatSubgroup_ne_top_of_prime_square_dvd (n := 25) (q := 5) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)

/--
For modulus 49, the Fermat subgroup is proper because the odd prime square 7²
divides it. Instantiate the prime-square theorem and verify the numerical premises by
normalization; this exercises the square-factor subgroup branch.
-/
example : fermatSubgroup 49 ≠ ⊤ := by
  exact
    fermatSubgroup_ne_top_of_prime_square_dvd (n := 49) (q := 7) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)

/--
For modulus 121, the Fermat subgroup is proper because the odd prime square 11²
divides it. Instantiate the prime-square theorem and verify the numerical premises by
normalization; this exercises the square-factor subgroup branch.
-/
example : fermatSubgroup 121 ≠ ⊤ := by
  exact
    fermatSubgroup_ne_top_of_prime_square_dvd (n := 121) (q := 11) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)

/--
For odd modulus 15, the canonical sign subgroup selected by factor 3 is proper.
The distinct primes 3 and 5 have product dividing the modulus; instantiate the
distinct-prime theorem and normalize its arithmetic premises. This exercises the CRT branch.
-/
example : signSubgroup 15 (2 ^ (padicValNat 2 (3 - 1) - 1) * Nat.divMaxPow (15 - 1) 2) ≠ ⊤ := by
  exact
    signSubgroup_ne_top_of_distinct_prime_dvd (n := 15) (q := 3) (r := 5) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

/--
For odd modulus 65, the canonical sign subgroup selected by factor 5 is proper.
The distinct primes 5 and 13 have product dividing the modulus; instantiate the
distinct-prime theorem and normalize its arithmetic premises. This exercises the CRT branch.
-/
example : signSubgroup 65 (2 ^ (padicValNat 2 (5 - 1) - 1) * Nat.divMaxPow (65 - 1) 2) ≠ ⊤ := by
  exact
    signSubgroup_ne_top_of_distinct_prime_dvd (n := 65) (q := 5) (r := 13) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

/--
For odd modulus 341, the canonical sign subgroup selected by factor 11 is proper.
The distinct primes 11 and 31 have product dividing the modulus; instantiate the
distinct-prime theorem and normalize its arithmetic premises. This exercises the CRT branch.
-/
example : signSubgroup 341 (2 ^ (padicValNat 2 (11 - 1) - 1) * Nat.divMaxPow (341 - 1) 2) ≠ ⊤ := by
  exact
    signSubgroup_ne_top_of_distinct_prime_dvd (n := 341) (q := 11) (r := 31) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

/--
For odd modulus 561, the canonical sign subgroup selected by factor 3 is proper.
The distinct primes 3 and 11 have product dividing the modulus; instantiate the
distinct-prime theorem and normalize its arithmetic premises. This exercises the CRT branch.
-/
example : signSubgroup 561 (2 ^ (padicValNat 2 (3 - 1) - 1) * Nat.divMaxPow (561 - 1) 2) ≠ ⊤ := by
  exact
    signSubgroup_ne_top_of_distinct_prime_dvd (n := 561) (q := 3) (r := 11) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

/--
For odd modulus 1729, the canonical sign subgroup selected by factor 7 is proper.
The distinct primes 7 and 13 have product dividing the modulus; instantiate the
distinct-prime theorem and normalize its arithmetic premises. This exercises the CRT branch.
-/
example : signSubgroup 1729 (2 ^ (padicValNat 2 (7 - 1) - 1) * Nat.divMaxPow (1729 - 1) 2) ≠ ⊤ := by
  exact
    signSubgroup_ne_top_of_distinct_prime_dvd (n := 1729) (q := 7) (r := 13) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

/--
For odd modulus 2047, the canonical sign subgroup selected by factor 23 is proper.
The distinct primes 23 and 89 have product dividing the modulus; instantiate the
distinct-prime theorem and normalize its arithmetic premises. This exercises the CRT branch.
-/
example :
    signSubgroup 2047 (2 ^ (padicValNat 2 (23 - 1) - 1) * Nat.divMaxPow (2047 - 1) 2) ≠ ⊤ := by
  exact
    signSubgroup_ne_top_of_distinct_prime_dvd (n := 2047) (q := 23) (r := 89) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)

end PseudoPrime.PrimeTest
