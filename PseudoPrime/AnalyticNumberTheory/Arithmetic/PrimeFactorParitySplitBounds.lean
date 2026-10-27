/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds

/-! # Prime support splitting with a parity saving -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a prime p different from two, p=1+2*(p/2).
Use the odd-prime remainder and Euclidean division. This makes the half-index map injective. -/
theorem prime_eq_one_add_two_div {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : p = 1 + 2 * (p / 2) := by
  have hm := Nat.mod_add_div p 2
  rw [hp.eq_two_or_odd.resolve_left hne] at hm
  exact hm.symm

/-- For a finite set of primes bounded by nonnegative y, its cardinality
is at most y/2+1. Remove two and inject the remaining odd primes by p/2 into a natural interval.
This improves the small-support count without an analytic prime-counting estimate. -/
theorem prime_finset_card_le_half_cutoff {s : Finset ℕ} {y : ℝ} (hy : 0 ≤ y)
    (hprime : ∀ p ∈ s, p.Prime) (hbound : ∀ p ∈ s, (p : ℝ) ≤ y) : (s.card : ℝ) ≤ y / 2 + 1 := by
  classical
  have hodd : (s.erase 2).card ≤ (Finset.Icc 1 ⌊y / 2⌋₊).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ ↦ p / 2)
    · intro p hp
      have hpprime := hprime p (Finset.mem_erase.mp hp).2
      have hpdiv := Nat.div_mul_le_self p 2
      have hcast : ((p / 2 : ℕ) : ℝ) * 2 ≤ p := by exact_mod_cast hpdiv
      exact
        Finset.mem_Icc.mpr
          ⟨(Nat.le_div_iff_mul_le (by decide : (0 : ℕ) < 2)).mpr
              (by simpa only [one_mul] using hpprime.two_le),
            Nat.le_floor
              (show ((p / 2 : ℕ) : ℝ) ≤ y / 2 by
                linarith only [hcast, hbound p (Finset.mem_erase.mp hp).2])⟩
    · intro p hp r hr he
      have hp' :=
        prime_eq_one_add_two_div (hprime p (Finset.mem_erase.mp hp).2) (Finset.mem_erase.mp hp).1
      have hr' :=
        prime_eq_one_add_two_div (hprime r (Finset.mem_erase.mp hr).2) (Finset.mem_erase.mp hr).1
      exact hp'.trans ((congrArg (fun k : ℕ ↦ 1 + 2 * k) he).trans hr'.symm)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hodd
  have htotal := Nat.le_add_of_sub_le (Finset.pred_card_le_card_erase (s := s) (a := 2))
  have htotalR : (s.card : ℝ) ≤ ((s.erase 2).card : ℝ) + 1 := by exact_mod_cast htotal
  have hoddR : ((s.erase 2).card : ℝ) ≤ ⌊y / 2⌋₊ := by exact_mod_cast hodd
  have hfloor := Nat.floor_le (div_nonneg hy (by norm_num only : (0 : ℝ) ≤ 2))
  linarith only [htotalR, hoddR, hfloor]

/-- For y ≥ 0, the number of distinct prime factors at most y is at most y/2+1.
Apply the finite-prime parity bound to the filtered support.
This is the small-factor input for the sharper support split. -/
theorem primeFactors_small_card_le_half_cutoff {q : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    ((q.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y)).card : ℝ) ≤ y / 2 + 1 := by
  exact
    prime_finset_card_le_half_cutoff hy
      (fun _ hp ↦ Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (fun _ hp ↦ (Finset.mem_filter.mp hp).2)

/-- For nonzero q and y > 1, the distinct-prime count is at most y/2+1+log q/log y.
Split the prime support and combine the parity count with the large-factor logarithmic weight.
This sharpens the elementary local-loss budget. -/
theorem primeFactors_card_le_half_cutoff_add_log_div {q : ℕ} (hq : q ≠ 0) {y : ℝ} (hy : 1 < y) :
    (q.primeFactors.card : ℝ) ≤ y / 2 + 1 + Real.log q / Real.log y := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := q.primeFactors) (fun p : ℕ ↦ (p : ℝ) ≤ y)
  have he :
    q.primeFactors.filter (fun p : ℕ ↦ ¬(p : ℝ) ≤ y) =
      q.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)) := by
    ext p
    simp only [Finset.mem_filter, not_le]
  have hcast :
    ((q.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y)).card : ℝ) +
        ((q.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ))).card : ℝ) =
      (q.primeFactors.card : ℝ) := by
    rw [he] at hc
    exact_mod_cast hc
  linarith only [hcast, primeFactors_small_card_le_half_cutoff (q := q) (zero_le_one.trans hy.le),
    primeFactors_large_card_le_log_div hq hy]

/-- For nonzero q, log q > 1 and theta > 0, splitting at (log q)^theta
bounds the prime count by half this power, one, and log q/(theta log log q).
Substitute the cutoff into the parity split. This supports rational logarithmic profiles. -/
theorem primeFactors_card_le_half_log_power {q : ℕ} (hq : q ≠ 0) (hL : 1 < Real.log q) {theta : ℝ}
    (ht : 0 < theta) :
    (q.primeFactors.card : ℝ) ≤
      (Real.log q) ^ theta / 2 + 1 + Real.log q / (theta * Real.log (Real.log q)) := by
  have h := primeFactors_card_le_half_cutoff_add_log_div hq (Real.one_lt_rpow hL ht)
  rw [Real.log_rpow (zero_lt_one.trans hL) theta] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
