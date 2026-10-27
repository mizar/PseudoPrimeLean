/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-! # Splitting the distinct prime support at a real cutoff

The logarithmic weight bounds the number of large prime factors. The small factors
fit into a natural interval. These estimates supply the modulus-loss budget in
the uniform Gamma subgroup comparison without parity or squarefreeness assumptions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For q ≠ 0 and y > 1, the number of prime factors exceeding y is at most
log q / log y. Sum their logarithmic weights and compare with the full support.
This controls the large-factor contribution to the uniform subgroup error. -/
theorem primeFactors_large_card_le_log_div {q : ℕ} (hq : q ≠ 0) {y : ℝ} (hy : 1 < y) :
    ((q.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ))).card : ℝ) ≤ Real.log q / Real.log y := by
  classical
  have hl : 0 < Real.log y := Real.log_pos hy
  have hs : ∑ p ∈ q.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log p ≤ Real.log q := by
    apply le_trans _ (sum_log_primeFactors_le_log hq)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp _
    exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).one_le)
  apply (le_div_iff₀ hl).2
  calc
    _ = ∑ _p ∈ q.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log y := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ q.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (zero_lt_one.trans hy) (Finset.mem_filter.mp hp).2.le
    _ ≤ Real.log q := hs

/-- For y ≥ 0, the number of prime factors at most y is at most y.
Embed the filtered support into the natural interval from 1 to floor y.
This bounds the small-factor contribution without estimating the prime density. -/
theorem primeFactors_small_card_le_cutoff {q : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    ((q.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y)).card : ℝ) ≤ y := by
  classical
  have hs : q.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y) ⊆ Finset.Icc 1 ⌊y⌋₊ := by
    intro p hp
    exact
      Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_le,
          Nat.le_floor (Finset.mem_filter.mp hp).2⟩
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  have hn : (q.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y)).card ≤ ⌊y⌋₊ := by
    simpa only [Nat.add_sub_cancel] using hc
  exact (Nat.cast_le.mpr hn).trans (Nat.floor_le hy)

/-- For q ≠ 0 and y > 1, the distinct prime count is at most y + log q / log y.
Split the support at y and combine the small- and large-factor bounds.
The uniform Gamma comparison uses this estimate for its nonunit loss. -/
theorem primeFactors_card_le_cutoff_add_log_div {q : ℕ} (hq : q ≠ 0) {y : ℝ} (hy : 1 < y) :
    (q.primeFactors.card : ℝ) ≤ y + Real.log q / Real.log y := by
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
  linarith only [hcast, primeFactors_small_card_le_cutoff (q := q) (zero_le_one.trans hy.le),
    primeFactors_large_card_le_log_div hq hy]

/-- For q ≠ 0, log q > 1 and theta > 0, split the prime support at
(log q)^theta. The count is at most this cutoff plus log q / (theta log log q).
This parametrizes later optimizations of the uniform subgroup budget. -/
theorem primeFactors_card_le_log_power {q : ℕ} (hq : q ≠ 0) (hL : 1 < Real.log q) {theta : ℝ}
    (ht : 0 < theta) :
    (q.primeFactors.card : ℝ) ≤
      (Real.log q) ^ theta + Real.log q / (theta * Real.log (Real.log q)) := by
  have h := primeFactors_card_le_cutoff_add_log_div hq (Real.one_lt_rpow hL ht)
  rw [Real.log_rpow (zero_lt_one.trans hL) theta] at h
  exact h

/-- For q ≠ 0 and log q > 1, the distinct prime count is at most
(log q)^(2/3) + (3/2) log q / log log q. Specialize the parameterized split.
This is the factor-count input for the uniform coefficient 4/5 plan. -/
theorem primeFactors_card_le_log_two_thirds {q : ℕ} (hq : q ≠ 0) (hL : 1 < Real.log q) :
    (q.primeFactors.card : ℝ) ≤
      (Real.log q) ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q) := by
  have h := primeFactors_card_le_log_power hq hL (by norm_num only : (0 : ℝ) < 2 / 3)
  have he :
    Real.log q / ((2 / 3 : ℝ) * Real.log (Real.log q)) =
      (3 / 2 : ℝ) * Real.log q / Real.log (Real.log q) := by
    rw [div_mul_eq_div_div]
    ring
  rw [he] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
