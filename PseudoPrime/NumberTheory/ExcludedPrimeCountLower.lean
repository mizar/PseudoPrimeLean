/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeCountPowerLower
public import Mathlib.Data.Nat.Squarefree

/-! # Prime counts after excluding the prime divisors of a modulus -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For q>0, the number of distinct prime factors is at most log(q)/log(2).
Their squarefree product divides q and is at least 2 to their number.
Take logarithms. This bounds the exclusion cost without a finite certificate. -/
theorem primeFactors_card_le_log_div_log_two {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
  have hp :=
    Finset.prod_le_prod (s := q.primeFactors) (f := fun _ ↦ (2 : ℕ)) (g := id)
      (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le)
  rw [Finset.prod_const] at hp
  have hpow : 2 ^ q.primeFactors.card ≤ q :=
    hp.trans (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
  have hR : (2 : ℝ) ^ q.primeFactors.card ≤ q := by exact_mod_cast hpow
  have hl := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) _) hR
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr hl

/-- For any cutoff B and modulus q, pi(B) is at most the number of primes
not dividing q below B plus the number of prime factors of q. Use the cardinality
of a finite-set difference. This separates eligible primes from excluded divisors. -/
theorem primeCounting_le_card_sdiff_primeFactors_add_card {B q : ℕ} :
    B.primeCounting ≤ (B.primesLE \ q.primeFactors).card + q.primeFactors.card := by
  rw [Finset.card_sdiff_add_card, ← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_le_card Finset.subset_union_left

/-- For 1<b<A, sufficiently large q has at least 2 log(q)^b primes below
floor(log(q)^A) not dividing q. Supply four times that many primes via Chebyshev
and absorb the at-most-linear prime-divisor count. No GRH or prime list is used. -/
theorem eventually_log_power_le_card_coprime_primes {b A : ℝ} (hb : 1 < b) (hbA : b < A) :
    Filter.Eventually
      (fun q : ℕ ↦
        2 * (Real.log q) ^ b ≤
          (((Nat.floor ((Real.log q) ^ A)).primesLE \ q.primeFactors).card : ℝ))
      Filter.atTop := by
  have hL : Filter.Tendsto (fun q : ℕ ↦ Real.log q) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpi :=
    hL.eventually
      (eventually_const_mul_rpow_le_primeCounting_floor_rpow (C := 4) (zero_lt_one.trans hb) hbA)
  have hsmall := hL.eventually (eventually_const_mul_rpow_le_rpow (b := 1) (C := 1 / Real.log 2) hb)
  filter_upwards [hpi, hsmall, Filter.eventually_gt_atTop (0 : ℕ)] with q hpiq hs hq
  have homega := primeFactors_card_le_log_div_log_two hq
  rw [Real.rpow_one] at hs
  have homega2 : (q.primeFactors.card : ℝ) ≤ (Real.log q) ^ b := by
    calc
      (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := homega
      _ = (1 / Real.log 2) * Real.log q := by ring
      _ ≤ (Real.log q) ^ b := hs
  have hc :=
    primeCounting_le_card_sdiff_primeFactors_add_card (B := Nat.floor ((Real.log q) ^ A)) (q := q)
  have hcR :
    (((Nat.floor ((Real.log q) ^ A)).primeCounting) : ℝ) ≤
      (((Nat.floor ((Real.log q) ^ A)).primesLE \ q.primeFactors).card : ℝ) +
        (q.primeFactors.card : ℝ) := by
    exact_mod_cast hc
  linarith only [hpiq, homega2, hcR]

end PseudoPrime.NumberTheory
