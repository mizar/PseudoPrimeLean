/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteLinearBudget
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Finite alternating cancellation for decreasing nonnegative weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For an antitone real sequence, an odd-length alternating prefix is at most its first term.
Compare consecutive odd prefixes by pairing the next negative and positive terms. This finite
estimate does not require convergence or a limit at infinity. -/
theorem alternating_odd_prefix_le_first {a : ℕ → ℝ} (ha : Antitone a) (k : ℕ) :
    (∑ j ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ j * a j) ≤ a 0 := by
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, Finset.sum_range_one, pow_zero, one_mul, le_refl]
  | succ k
    ih =>
    have he : (-1 : ℝ) ^ (2 * k) = 1 := by
      rw [pow_mul]
      norm_num only [neg_one_sq, one_pow]
    have ho : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, he]; norm_num only
    have hn : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
      rw [pow_succ, ho]; norm_num only
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, hn, ho, one_mul, neg_one_mul]
    have h := ha (Nat.le_succ (2 * k + 1))
    linarith only [ih, h]

/-- For a nonnegative antitone real sequence, every finite alternating prefix is at most its
first term. Separate even and odd lengths and apply the odd-prefix estimate; this is the upper
cancellation bound for prime-power costs. -/
theorem alternating_prefix_le_first {a : ℕ → ℝ} (ha : Antitone a) (h0 : ∀ k, 0 ≤ a k) (N : ℕ) :
    (∑ j ∈ Finset.range N, (-1 : ℝ) ^ j * a j) ≤ a 0 := by
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨k, hk⟩ := he
    rw [hk, ← two_mul]
    cases k with
    | zero => simpa only [Nat.mul_zero, Finset.sum_range_zero] using h0 0
    | succ
      k =>
      have he : (-1 : ℝ) ^ (2 * k) = 1 := by
        rw [pow_mul]
        norm_num only [neg_one_sq, one_pow]
      have ho : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
        rw [pow_succ, he]; norm_num only
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, ho, neg_one_mul]
      have h := alternating_odd_prefix_le_first ha k
      linarith only [h, h0 (2 * k + 1)]
  · obtain ⟨k, hk⟩ := ho
    rw [hk]
    exact alternating_odd_prefix_le_first ha k

/-- For a nonnegative sequence decreasing on positive indices, twice the odd-index weight sum up
to K is at most the total prefix plus the first weight. Rewrite the parity coefficient as an
alternating sign and shift the finite interval to a range. This keeps square-power cancellation
before bounding an exclusion budget. -/
theorem odd_weighted_prefix_le_total_add_first {a : ℕ → ℝ} (ha : Antitone (fun j ↦ a (j + 1)))
    (h0 : ∀ j, 0 ≤ a (j + 1)) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (if Even k then (0 : ℝ) else 2) * a k) ≤
      (∑ k ∈ Finset.Icc 1 K, a k) + a 1 := by
  have hc (k : ℕ) : (if Even k then (0 : ℝ) else 2) = 1 + (-1 : ℝ) ^ (k + 1) := by
    by_cases he : Even k
    · rw [ite_eq_left he, pow_succ, he.neg_one_pow]
      norm_num only
    · have ho := Nat.not_even_iff_odd.mp he
      rw [ite_eq_right he, pow_succ, ho.neg_one_pow]
      norm_num only
  have he :
    (∑ k ∈ Finset.Icc 1 K, (if Even k then (0 : ℝ) else 2) * a k) =
      (∑ k ∈ Finset.Icc 1 K, a k) + ∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * a k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hc]
    ring
  have hi : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  have hs :
    (∑ k ∈ Finset.Icc 1 K, (-1 : ℝ) ^ (k + 1) * a k) =
      ∑ j ∈ Finset.range K, (-1 : ℝ) ^ j * a (j + 1) := by
    rw [hi, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm 1 j, show j + 1 + 1 = j + 2 by ring, pow_add]
    norm_num only [neg_one_sq, mul_one]
  have hb := alternating_prefix_le_first ha h0 K
  rw [he]
  linarith only [hs, hb]

/-- For nonnegative coefficients and geometric bases b at least one and d at least two, the
displayed combined weight decreases at every positive index. Compare denominators and use k+1 at
most kd. This controls Euler weights containing an exponent factor. -/
theorem geometric_log_weight_succ_le {A B b d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 1 ≤ b)
    (hd : 2 ≤ d) {k : ℕ} (hk : 1 ≤ k) :
    A / b ^ (k + 1) + B * (k + 1 : ℕ) / d ^ (k + 1) ≤ A / b ^ k + B * (k : ℕ) / d ^ k := by
  have hb0 : 0 < b := by linarith only [hb]
  have hd0 : 0 < d := by linarith only [hd]
  have hf := div_le_div_of_nonneg_left hA (pow_pos hb0 k) (pow_le_pow_right₀ hb (Nat.le_succ k))
  have hk0 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  have hn : (k : ℝ) + 1 ≤ k * d := by nlinarith only [hk0, hd]
  have hm := mul_le_mul_of_nonneg_left hn hB
  have hs : B * (k + 1 : ℕ) / d ^ (k + 1) ≤ B * (k : ℕ) / d ^ k := by
    apply (div_le_div_iff₀ (pow_pos hd0 (k + 1)) (pow_pos hd0 k)).mpr
    rw [pow_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    have ht := mul_le_mul_of_nonneg_right hm (pow_nonneg hd0.le k)
    nlinarith only [ht]
  exact add_le_add hf hs

/-- The combined geometric and exponent-weighted sequence is antitone from positive index one
onward under the stated sign and base assumptions. Apply the one-step decrease criterion. This
reusable form supplies the monotonicity needed in truncated prime-power prefixes. -/
theorem geometric_log_weight_antitone {A B b d : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 1 ≤ b)
    (hd : 2 ≤ d) : Antitone (fun j : ℕ ↦ A / b ^ (j + 1) + B * (j + 1 : ℕ) / d ^ (j + 1)) := by
  apply antitone_nat_of_succ_le
  intro j
  exact geometric_log_weight_succ_le hA hB hb hd (Nat.succ_le_succ (Nat.zero_le j))

end PseudoPrime.Analysis
