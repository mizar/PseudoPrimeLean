/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Explicit logarithmic bounds for distinct prime-factor counts

Separating the prime factors two, three, and five improves the common-factor
correction used in the LLS coset prime bound.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A prime outside the finite set consisting of two, three, and five is at least seven.
Check the possible smaller natural values; this isolates all positive logarithmic
deficits in the prime-factor count estimate. -/
private theorem prime_ge_seven_of_not_small {p : ℕ} (hp : p.Prime) (hs : p ∉ ({2,3,5} : Finset ℕ)) :
    7 ≤ p := by
  by_contra hn
  have hb : p ≤ 6 := Nat.le_of_lt_succ (lt_of_not_ge hn)
  interval_cases p <;>
    first
    | exact (hs (by decide)).elim
    | norm_num only at hp

/-- For a nonzero natural number, its prime-factor count times the logarithm of seven
is at most its logarithm plus the deficits of two, three, and five. Sum the deficits,
discard nonpositive contributions from larger primes, and use the product of distinct
prime factors. This gives a uniform count bound without a primorial certificate. -/
theorem card_primeFactors_mul_log_seven_le {n : ℕ} (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) * Real.log 7 ≤
      Real.log n + 3 * Real.log 7 - (Real.log 2 + Real.log 3 + Real.log 5) := by
  classical
  let S : Finset ℕ := {2,3,5}
  let f := fun p : ℕ ↦ Real.log 7 - Real.log p
  have hpoint (p : ℕ) (hp : p ∈ n.primeFactors) : f p ≤ if p ∈ S then f p else 0 := by
    by_cases hs : p ∈ S
    · rw [ite_eq_left hs]
    · rw [ite_eq_right hs]
      exact
        sub_nonpos.mpr
          (Real.log_le_log (by norm_num only : (0 : ℝ) < 7)
            (by exact_mod_cast prime_ge_seven_of_not_small (Nat.prime_of_mem_primeFactors hp) hs))
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.sum_filter] at hsum
  have hsub : n.primeFactors.filter (fun p ↦ p ∈ S) ⊆ S := fun p hp ↦ (Finset.mem_filter.mp hp).2
  have hnonneg : ∀ p ∈ S, 0 ≤ f p := by
    intro p hp
    have hp' : p = 2 ∨ p = 3 ∨ p = 5 := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hp
    rcases hp' with rfl | rfl | rfl <;>
      exact sub_nonneg.mpr (Real.log_le_log (by norm_num only) (by norm_num only))
  have hfull := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ ↦ hnonneg p hp)
  have hlog := sum_log_primeFactors_le_log hn
  have hfinal := hsum.trans hfull
  simp only [f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hfinal
  have hc : S.card = 3 := by decide
  have he : (∑ p ∈ S, Real.log p) = Real.log 2 + Real.log 3 + Real.log 5 := by
    dsimp only [S]
    rw [Finset.sum_insert (by decide : (2 : ℕ) ∉ {3,5}),
      Finset.sum_insert (by decide : (3 : ℕ) ∉ {5}), Finset.sum_singleton]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hc, he] at hfinal
  norm_num only [Nat.cast_ofNat] at hfinal
  linarith only [hfinal, hlog]

/-- A natural number at least twenty thousand has at most two thirds of its logarithm
distinct prime factors. Counts at most five use the level lower bound. Larger counts
use the logarithmic deficit estimate at seven and rational bounds on logarithms.
This sharpens the common-factor error in the explicit coset prime bound. -/
theorem card_primeFactors_le_two_thirds_log {n : ℕ} (hn : 20000 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ (2 / 3 : ℝ) * Real.log n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num only) hn)
  have hlog : (9 : ℝ) ≤ Real.log n := by
    have hm :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 19683)
        (show (19683 : ℝ) ≤ n by exact_mod_cast (by linarith only [hn] : 19683 ≤ n))
    rw [show (19683 : ℝ) = 3 ^ 9 by norm_num only, Real.log_pow] at hm
    norm_num only at hm
    linarith only [hm, Real.log_three_gt_d9]
  by_cases hc : n.primeFactors.card ≤ 5
  · have hcr : (n.primeFactors.card : ℝ) ≤ 5 := by exact_mod_cast hc
    linarith only [hcr, hlog]
  · have hcr : (6 : ℝ) ≤ n.primeFactors.card := by
      exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hc)
    have h6 : (179 / 100 : ℝ) < Real.log 6 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only)]
      linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
    have ha :=
      Analysis.log_gt_affine_of_anchor (a := 6) (b := 7) (y := 7) (by norm_num only)
        (by norm_num only) (by norm_num only) (le_refl _) h6
    have h7 : (193 / 100 : ℝ) ≤ Real.log 7 := by
      norm_num only at ha; linarith only [ha]
    have h5 :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 9 / 2) (by norm_num only : (9 / 2 : ℝ) ≤ 5)
    rw [Real.log_div (by norm_num only) (by norm_num only), show (9 : ℝ) = 3 ^ 2 by norm_num only,
      Real.log_pow] at h5
    norm_num only at h5
    have hf := card_primeFactors_mul_log_seven_le hn0
    have hm :=
      mul_le_mul_of_nonneg_left h7 (show (0 : ℝ) ≤ n.primeFactors.card - 3 by linarith only [hcr])
    nlinarith only [hf, hm, h5, hcr, Real.log_three_gt_d9]

/-- For a level at least twenty thousand, a positive cutoff and positive scale whose
product with the level logarithm is at most the cutoff square root, the common-factor
logarithmic sum is at most the square root times the squared cutoff logarithm divided
by three times the scale. Combine the count bound with the finite common-factor
estimate; the scale is the subgroup index minus one in the coset argument. -/
theorem commonFactorLogWeightedSum_le_sqrt_log_square {q : ℕ} (hq : 20000 ≤ q) {x d : ℝ}
    (hx : 0 < x) (hd : 0 < d) (hs : d * Real.log q ≤ Real.sqrt x) :
    commonFactorLogWeightedSum x q ≤ Real.sqrt x / (3 * d) * (Real.log x) ^ 2 := by
  have hc := card_primeFactors_le_two_thirds_log hq
  have hb := commonFactorLogWeightedSum_le (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num only) hq)) hx
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log x))
  have hs' := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hs)
  have ht := mul_le_mul_of_nonneg_right hs' (sq_nonneg (Real.log x))
  have he : Real.sqrt x / (3 * d) = (Real.sqrt x / d) / 3 := by ring
  rw [he]
  nlinarith only [hb, hm, ht]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
