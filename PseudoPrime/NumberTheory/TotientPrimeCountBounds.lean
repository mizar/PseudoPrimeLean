/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-! Totient ratio lower bounds indexed by the number of distinct prime factors. -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Choose a positive normalization with r^N≤r^s.card and a finite
exception set. Exceptional factors lie in [0,r] and all remaining factors are
at least r. Normalize the exceptions and compare products to obtain a lower
bound. This shares the totient estimates and the six-prime product bound. -/
private theorem prod_lower_bound_of_normalized_exceptions {s t : Finset ℕ} {N : ℕ} {r : ℚ}
    (f : ℕ → ℚ) (hr : 0 < r) (hpow : r ^ N ≤ r ^ s.card) (ht : ∀ p ∈ t, 0 ≤ f p ∧ f p ≤ r)
    (hout : ∀ p ∈ s, p ∉ t → r ≤ f p) : r ^ N * (∏ p ∈ t, f p / r) ≤ ∏ p ∈ s, f p := by
  let v : ℕ → ℚ := fun p ↦ if p ∈ t then f p / r else 1
  have hv : ∀ p ∈ t, 0 ≤ v p ∧ v p ≤ 1 := by
    intro p hp
    simp only [v, ite_eq_left hp]
    exact ⟨div_nonneg (ht p hp).1 hr.le, (div_le_one hr).mpr (ht p hp).2⟩
  have hv0 : ∀ p, 0 ≤ v p := by
    intro p
    by_cases hp : p ∈ t
    · exact (hv p hp).1
    · simp only [v, ite_eq_right hp, zero_le_one]
  have hpoint : ∀ p ∈ s, r * v p ≤ f p := by
    intro p hp
    by_cases hpt : p ∈ t
    · simp only [v, ite_eq_left hpt]
      exact (mul_div_cancel₀ (f p) hr.ne').le
    · simpa only [v, ite_eq_right hpt, mul_one] using hout p hp hpt
  have hprod := Finset.prod_le_prod₀ (fun p _ ↦ mul_nonneg hr.le (hv0 p)) hpoint
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have hvt : (∏ p ∈ t, v p) ≤ ∏ p ∈ s ∩ t, v p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right (fun p hp ↦ (hv p hp).1)
      (fun p hp _ ↦ (hv p hp).2)
  have hvs : (∏ p ∈ t, v p) ≤ ∏ p ∈ s, v p := by
    simpa only [v, Finset.prod_ite_mem, Finset.inter_assoc, Finset.inter_self] using hvt
  have hp := mul_le_mul hpow hvs (Finset.prod_nonneg (fun p _ ↦ hv0 p)) (pow_nonneg hr.le _)
  have he : (∏ p ∈ t, v p) = ∏ p ∈ t, f p / r := Finset.prod_congr rfl (fun p hp ↦ ite_eq_left hp)
  rw [he] at hp
  exact hp.trans hprod

/-- Prime cutoff for the normalization associated with N distinct prime factors.
For N from one through five it is 2,3,5,7,11; other inputs use eleven.
Primes below the cutoff form the finite exceptions in the product estimate. -/
private def totientPrimeCountCutoff (N : ℕ) : ℕ :=
  match N with
  | 1 => 2
  | 2 => 3
  | 3 => 5
  | 4 => 7
  | _ => 11

/-- Normalization (p-1)/p at the prime cutoff for N factors. Its values for
N from one through five are 1/2,2/3,4/5,6/7,10/11; other inputs use 10/11.
Factors at larger primes are at least this value. -/
private def totientPrimeCountNormalization (N : ℕ) : ℚ :=
  match N with
  | 1 => 1 / 2
  | 2 => 2 / 3
  | 3 => 4 / 5
  | 4 => 6 / 7
  | _ => 10 / 11

/-- The primes below the normalization cutoff. For counts one through five
these are the first zero through four primes; other inputs use {2,3,5,7}.
Only these factors can reduce the normalized product below one. -/
private def totientExceptionalPrimes (N : ℕ) : Finset ℕ :=
  match N with
  | 1 => ∅
  | 2 => {2}
  | 3 => {2, 3}
  | 4 => {2, 3, 5}
  | _ => {2, 3, 5, 7}

/-- Certified totient-to-modulus ratio for an upper bound N on distinct prime
factors. For 1≤N≤5 the values are 1/2,1/3,4/15,8/35,16/77. Other inputs return
16/77, but the soundness theorem requires 1≤N≤5. Multiply this rational coefficient
by the modulus to obtain the lower bound used in residue interval certificates. -/
def totientPrimeCountLowerRatio (N : ℕ) : ℚ :=
  match N with
  | 1 => 1 / 2
  | 2 => 1 / 3
  | 3 => 4 / 15
  | 4 => 8 / 35
  | _ => 16 / 77

/-- For counts from one through five, the normalization is positive, at most
one and equals one minus the inverse cutoff prime. Check the five rational cases.
These properties supply the common product estimate and its inverse comparison. -/
private theorem totientPrimeCountNormalization_bounds {N : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 5) :
    0 < totientPrimeCountNormalization N ∧
      totientPrimeCountNormalization N ≤ 1 ∧
      totientPrimeCountNormalization N = 1 - (totientPrimeCountCutoff N : ℚ)⁻¹ := by
  interval_cases N <;> decide +kernel

/-- At counts one through five, each exceptional totient factor is nonnegative
and at most the normalization. Check the finite prime sets by kernel computation.
This provides the exceptional-product hypotheses. -/
private theorem totientExceptionalPrimes_factors {N : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 5) :
    ∀ p ∈ totientExceptionalPrimes N,
      (0 : ℚ) ≤ 1 - (p : ℚ)⁻¹ ∧ 1 - (p : ℚ)⁻¹ ≤ totientPrimeCountNormalization N := by
  interval_cases N <;> decide +kernel

/-- For counts one through five, a prime outside the exception set is at least
the cutoff. Exclude the smaller nonprime integers by kernel computation.
This bounds every nonexceptional totient factor by the normalization. -/
private theorem prime_ge_totientPrimeCountCutoff {N p : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 5) (hp : p.Prime)
    (hn : p ∉ totientExceptionalPrimes N) : totientPrimeCountCutoff N ≤ p := by
  interval_cases N <;> simp only [totientPrimeCountCutoff]
  all_goals
    by_contra hh
    have hhi := Nat.le_of_lt_succ (Nat.lt_of_not_ge hh)
    have hlo := hp.two_le
    interval_cases p <;>
      first
      | exact hn (by decide)
      | exact (by decide : ¬Nat.Prime _) hp

/-- For counts from one through five, the ratio equals the normalization to
that count times the product of normalized exceptions. Check the five rational
identities in the kernel. This identifies the constant in the common product bound. -/
private theorem totientPrimeCountLowerRatio_normalization {N : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 5) :
    totientPrimeCountLowerRatio N =
      totientPrimeCountNormalization N ^ N *
        (∏ p ∈ totientExceptionalPrimes N, (1 - (p : ℚ)⁻¹) / totientPrimeCountNormalization N) := by
  interval_cases N <;> decide +kernel

/-- For a finite set of primes of cardinality at most N, with 1≤N≤5, its Euler
factors have product at least the prime-count ratio. Bound nonexceptional primes
by the cutoff, compare their inverses and apply the normalized product theorem.
This gives all five ratio estimates from one proof. -/
theorem prod_totient_factors_ge_primeCount_ratio (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) {N : ℕ}
    (hN : 1 ≤ N) (hN' : N ≤ 5) (hc : s.card ≤ N) :
    totientPrimeCountLowerRatio N ≤ ∏ p ∈ s, (1 - (p : ℚ)⁻¹) := by
  have hr := totientPrimeCountNormalization_bounds hN hN'
  have hout p (hps : p ∈ s) (hpt : p ∉ totientExceptionalPrimes N) :
    totientPrimeCountNormalization N ≤ 1 - (p : ℚ)⁻¹ := by
    have hb : (totientPrimeCountCutoff N : ℚ) ≤ p :=
      Nat.cast_le.mpr (prime_ge_totientPrimeCountCutoff hN hN' (hp p hps) hpt)
    have hcut : (0 : ℚ) < totientPrimeCountCutoff N := by interval_cases N <;> decide +kernel
    rw [hr.2.2]
    exact sub_le_sub_left ((inv_le_inv₀ (hcut.trans_le hb) hcut).mpr hb) 1
  rw [totientPrimeCountLowerRatio_normalization hN hN']
  exact
    prod_lower_bound_of_normalized_exceptions (fun p ↦ 1 - (p : ℚ)⁻¹) hr.1
      (pow_le_pow_of_le_one hr.1.le hr.2.1 hc) (totientExceptionalPrimes_factors hN hN') hout

/-- If a modulus has at most N distinct prime factors and 1≤N≤5, its totient
is at least the rational prime-count ratio times the modulus. Apply the finite
Euler-factor bound and multiply by the nonnegative modulus in Euler's formula.
This is the rational arithmetic input to interval certificates. -/
theorem totient_ge_primeCount_ratio {q N : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 5)
    (hc : q.primeFactors.card ≤ N) : totientPrimeCountLowerRatio N * q ≤ q.totient := by
  have hb :=
    prod_totient_factors_ge_primeCount_ratio q.primeFactors
      (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) hN hN' hc
  rw [Nat.totient_eq_mul_prod_factors]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg q)

/-- For a modulus with at most N distinct prime factors and 1≤N≤5, the real
coercion of the ratio times the modulus is at most its totient. Cast the rational
Euler-product estimate. This supplies the real lower bound to analytic intervals. -/
theorem totient_ge_primeCount_ratio_real {q N : ℕ} (hN : 1 ≤ N) (hN' : N ≤ 5)
    (hc : q.primeFactors.card ≤ N) : (totientPrimeCountLowerRatio N : ℝ) * q ≤ q.totient := by
  exact_mod_cast totient_ge_primeCount_ratio hN hN' hc

/-- A set of at least six distinct primes has product at least 30030.
Normalize by thirteen and retain the five smaller primes as exceptions.
This bounds the number of prime factors of small moduli. -/
theorem prod_primes_ge_primorial_six (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime) (hc : 6 ≤ s.card) :
    30030 ≤ ∏ p ∈ s, p := by
  let t : Finset ℕ := {2, 3, 5, 7, 11}
  have ht : ∀ p ∈ t, (0 : ℚ) ≤ p ∧ (p : ℚ) ≤ 13 := by decide +kernel
  have hsmall : ∀ p ∈ Finset.Icc 2 12, p.Prime → p ∈ t := by decide +kernel
  have hout p (hps : p ∈ s) (hpt : p ∉ t) : (13 : ℚ) ≤ p := by
    have h13 : 13 ≤ p := by
      by_contra hh
      exact
        hpt
          (hsmall p
            (Finset.mem_Icc.mpr ⟨(hp p hps).two_le, Nat.le_of_lt_succ (Nat.lt_of_not_ge hh)⟩)
            (hp p hps))
    exact_mod_cast h13
  have hb :=
    prod_lower_bound_of_normalized_exceptions (s := s) (t := t) (N := 6) (r := 13) (fun p ↦ (p : ℚ))
      (by decide) (pow_le_pow_right₀ (by decide : (1 : ℚ) ≤ 13) hc) ht hout
  have he : (13 : ℚ) ^ 6 * (∏ p ∈ t, (p : ℚ) / 13) = 30030 := by decide +kernel
  rw [he] at hb
  rw [← Nat.cast_prod] at hb
  exact_mod_cast hb

/-- A natural number below 30030 has at most five distinct prime factors.
Six factors would have product at least 30030, while their product divides
and is at most the positive modulus. The zero case has no prime factors.
This supplies the prime-count cutoff for finite analytic intervals. -/
theorem primeFactors_card_le_five_of_lt_primorial_six {q : ℕ} (hq : q < 30030) :
    q.primeFactors.card ≤ 5 := by
  by_cases hq0 : q = 0
  · subst q
    decide +kernel
  · by_contra hh
    have hc : 6 ≤ q.primeFactors.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge hh)
    have hp :=
      prod_primes_ge_primorial_six q.primeFactors (fun _ h ↦ Nat.prime_of_mem_primeFactors h) hc
    have hl := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.prod_primeFactors_dvd q)
    exact (not_lt_of_ge (hp.trans hl)) hq

end PseudoPrime.NumberTheory
