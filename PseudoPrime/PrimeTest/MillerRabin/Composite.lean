/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-!
# Prime-factor cases for composite moduli
-/

namespace PseudoPrime.PrimeTest

/--
Every composite natural modulus greater than one has a prime-square divisor or two distinct prime
divisors whose product divides it. This elementary split selects the appropriate subgroup
construction below and does not assume that `n` is squarefree.
-/
theorem prime_square_or_distinct_primes_dvd {n : ℕ}
    (hn : 1 < n)
    (hnComposite : ¬ Nat.Prime n) :
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
private theorem odd_prime_factor_ne_two {n q : ℕ}
    (hnOdd : Odd n) (hq : Nat.Prime q) (hqdiv : q ∣ n) : q ≠ 2 := by
  intro hqEq
  subst q
  exact (Nat.not_even_iff_odd.mpr hnOdd) (even_iff_two_dvd.mpr hqdiv)

/-- The standard factorization of `q - 1` has odd part and a positive two-adic exponent. -/
private theorem prime_sub_two_adic_decomposition {q : ℕ}
    (hq : Nat.Prime q) (hq2 : q ≠ 2) :
    ∃ t c : ℕ, q - 1 = 2 ^ t * c ∧ Odd c ∧ 0 < t := by
  let t := twoAdicExponent (q - 1)
  let c := oddPart (q - 1)
  have hqdecomp : q - 1 = 2 ^ t * c := by
    dsimp [t, c]
    exact (twoAdicPart_mul_oddPart (q - 1)).symm
  have hcOdd : Odd c := oddPart_odd (Nat.sub_ne_zero_of_lt hq.one_lt)
  have ht : 0 < t := by
    have hqOdd : Odd q := hq.odd_of_ne_two hq2
    have hqminusEven : Even (q - 1) := by
      rcases hqOdd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    by_contra htn
    have htzero : t = 0 := Nat.eq_zero_of_not_pos htn
    have hceq : c = q - 1 := by
      rw [htzero] at hqdecomp
      simp at hqdecomp
      exact hqdecomp.symm
    apply (Nat.not_even_iff_odd.mpr hcOdd)
    rw [hceq]
    exact hqminusEven
  exact ⟨t, c, hqdecomp, hcOdd, ht⟩

/--
Every odd composite modulus has a proper subgroup containing every residue that passes its
strong Miller–Rabin condition. The prime-factor split selects the Fermat subgroup when a square
divides `n`, and the sign-power subgroup for two distinct prime divisors. The full residue-to-unit
image condition is the form consumed by the later LLS argument.
-/
theorem exists_proper_subgroup_containing_strongMillerRabinPass {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnComposite : ¬ Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H ≠ ⊤ ∧
        ∀ x : ZMod n,
          StrongMillerRabinPass n s d x →
            ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = x := by
  rcases prime_square_or_distinct_primes_dvd hn hnComposite with hsquare | hdifferent
  · obtain ⟨q, hq, hq2div⟩ := hsquare
    have hqdiv : q ∣ n := dvd_trans (by exact ⟨q, by rw [pow_two]⟩) hq2div
    have hq2 := odd_prime_factor_ne_two hnOdd hq hqdiv
    refine ⟨fermatSubgroup n, fermatSubgroup_ne_top_of_prime_square_dvd hn hq hq2 hq2div,
      ?_⟩
    intro x hpass
    exact strongMillerRabinPass_mem_fermatSubgroup hn hdecomp hpass
  · obtain ⟨q, r, hq, hr, hqr, hdiv⟩ := hdifferent
    have hqdiv : q ∣ n := dvd_trans ⟨r, rfl⟩ hdiv
    have hrdiv : r ∣ n := dvd_trans ⟨q, by ring⟩ hdiv
    have hq2 := odd_prime_factor_ne_two hnOdd hq hqdiv
    have hr2 := odd_prime_factor_ne_two hnOdd hr hrdiv
    obtain ⟨t, c, hqdecomp, hcOdd, ht⟩ := prime_sub_two_adic_decomposition hq hq2
    let H := signSubgroup n (2 ^ (t - 1) * d)
    refine ⟨H, ?_, ?_⟩
    · exact signSubgroup_ne_top_of_distinct_prime_dvd hn hq hr hq2 hr2 hqr hdiv
        hqdecomp hdOdd ht
    · intro x hpass
      exact strongMillerRabinPass_mem_signSubgroup hn hdecomp hpass hq hq2 hqdiv
        hqdecomp hcOdd

example : fermatSubgroup 9 ≠ ⊤ := by
  exact fermatSubgroup_ne_top_of_prime_square_dvd (n := 9) (q := 3)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : fermatSubgroup 25 ≠ ⊤ := by
  exact fermatSubgroup_ne_top_of_prime_square_dvd (n := 25) (q := 5)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : fermatSubgroup 49 ≠ ⊤ := by
  exact fermatSubgroup_ne_top_of_prime_square_dvd (n := 49) (q := 7)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : fermatSubgroup 121 ≠ ⊤ := by
  exact fermatSubgroup_ne_top_of_prime_square_dvd (n := 121) (q := 11)
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : signSubgroup 15 1 ≠ ⊤ := by
  exact signSubgroup_ne_top_of_distinct_prime_dvd (n := 15) (q := 3) (r := 5)
    (t := 1) (c := 1) (d := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : signSubgroup 65 2 ≠ ⊤ := by
  exact signSubgroup_ne_top_of_distinct_prime_dvd (n := 65) (q := 5) (r := 13)
    (t := 2) (c := 1) (d := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : signSubgroup 341 1 ≠ ⊤ := by
  exact signSubgroup_ne_top_of_distinct_prime_dvd (n := 341) (q := 11) (r := 31)
    (t := 1) (c := 5) (d := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : signSubgroup 561 1 ≠ ⊤ := by
  exact signSubgroup_ne_top_of_distinct_prime_dvd (n := 561) (q := 3) (r := 11)
    (t := 1) (c := 1) (d := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : signSubgroup 1729 1 ≠ ⊤ := by
  exact signSubgroup_ne_top_of_distinct_prime_dvd (n := 1729) (q := 7) (r := 13)
    (t := 1) (c := 3) (d := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : signSubgroup 2047 1 ≠ ⊤ := by
  exact signSubgroup_ne_top_of_distinct_prime_dvd (n := 2047) (q := 23) (r := 89)
    (t := 1) (c := 11) (d := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end PseudoPrime.PrimeTest
