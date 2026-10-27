/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Finite second moments from cubic tail bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For natural K<=n the rational sum of 2k+1 over K<=k<n is n^2-K^2.
Write each term as the difference of consecutive squares and telescope. -/
theorem sum_odd_Ico_rat {K n : ℕ} (h : K ≤ n) :
    (∑ k ∈ Finset.Ico K n, (2 * (k : ℚ) + 1)) = (n : ℚ) ^ 2 - (K : ℚ) ^ 2 := by
  have he :
    (∑ k ∈ Finset.Ico K n, (2 * (k : ℚ) + 1)) =
      ∑ k ∈ Finset.Ico K n, (((k + 1 : ℕ) : ℚ) ^ 2 - (k : ℚ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.cast_add, Nat.cast_one]
    ring
  exact he.trans (Finset.sum_Ico_sub (fun k ↦ (k : ℚ) ^ 2) h)

/-- For n<=P, bound n^2 by K*n plus its tail layer sum above K.
Below K use n^2<=K*n; above K telescope the odd increments and extend by zero. -/
theorem square_le_mass_add_tail {n K P : ℕ} (hn : n ≤ P) :
    (n : ℚ) ^ 2 ≤ (K : ℚ) * n + ∑ k ∈ Finset.Ico K P, if k < n then 2 * (k : ℚ) + 1 else 0 := by
  by_cases hnk : n ≤ K
  · have hz : (∑ k ∈ Finset.Ico K P, if k < n then 2 * (k : ℚ) + 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact ite_eq_right (fun hlt ↦ (hnk.trans (Finset.mem_Ico.mp hk).1).not_gt hlt)
    rw [hz, add_zero]
    have hc : (n : ℚ) ≤ K := Nat.cast_le.mpr hnk
    nlinarith only [hc, (Nat.cast_nonneg n : (0 : ℚ) ≤ n)]
  · have hkn : K ≤ n := (Nat.lt_of_not_ge hnk).le
    have he :
      (∑ k ∈ Finset.Ico K n, (2 * (k : ℚ) + 1)) =
        ∑ k ∈ Finset.Ico K P, if k < n then 2 * (k : ℚ) + 1 else 0 := by
      calc
        _ = ∑ k ∈ Finset.Ico K n, if k < n then 2 * (k : ℚ) + 1 else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (ite_eq_left (Finset.mem_Ico.mp hk).2).symm
        _ = _ := by
          apply Finset.sum_subset (Finset.Ico_subset_Ico le_rfl hn)
          intro k hk hnot
          apply ite_eq_right
          intro hlt
          exact hnot (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1, hlt⟩)
    rw [← he, sum_odd_Ico_rat hkn]
    have hc : (K : ℚ) ≤ n := Nat.cast_le.mpr hkn
    nlinarith only [hc, (Nat.cast_nonneg K : (0 : ℚ) ≤ K)]

/-- For positive k and H*(k+1)^3<=C, bound the weighted tail (2k+1)H
by 2C*(1/k-1/(k+1)). Clear positive denominators and retain the nonnegative remainder. -/
theorem cubic_tail_term_le {k H C : ℕ} (hk : 0 < k) (hC : H * (k + 1) ^ 3 ≤ C) :
    (2 * (k : ℚ) + 1) * H ≤ 2 * C * (1 / (k : ℚ) - 1 / ((k : ℚ) + 1)) := by
  have hkq : (0 : ℚ) < k := Nat.cast_pos.mpr hk
  have hs : (0 : ℚ) < (k : ℚ) + 1 := by linarith only [hkq]
  have hid : 1 / (k : ℚ) - 1 / ((k : ℚ) + 1) = 1 / ((k : ℚ) * ((k : ℚ) + 1)) := by
    field_simp [ne_of_gt hkq, ne_of_gt hs]
    ring
  rw [hid, mul_one_div]
  apply (le_div_iff₀ (mul_pos hkq hs)).mpr
  have hc : (H : ℚ) * ((k : ℚ) + 1) ^ 3 ≤ C := by
    have he : ((H * (k + 1) ^ 3 : ℕ) : ℚ) ≤ (C : ℚ) := Nat.cast_le.mpr hC
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using he
  have hg : (0 : ℚ) ≤ H * ((k : ℚ) + 1) * (3 * (k : ℚ) + 2) := by
    apply mul_nonneg (mul_nonneg (Nat.cast_nonneg H) hs.le)
    linarith only [hkq]
  nlinarith only [hc, hg]

/-- For a finite natural-valued family bounded by P, positive K<=P, and
cubic tail counts bounded by C above K, prove K*sum(N^2)<=K^2*sum(N)+2C over rationals.
Sum the layer bound, interchange finite sums, and telescope reciprocal differences. -/
theorem sum_squares_le_of_cubic_tail {ι : Type*} [Fintype ι] (N : ι → ℕ) (P K C : ℕ)
    (hN : ∀ a, N a ≤ P) (hK : 0 < K) (hKP : K ≤ P)
    (htail :
      ∀ k ∈ Finset.Ico K P, (Finset.univ.filter (fun a ↦ k + 1 ≤ N a)).card * (k + 1) ^ 3 ≤ C) :
    (K : ℚ) * (∑ a, (N a : ℚ) ^ 2) ≤ (K : ℚ) ^ 2 * (∑ a, (N a : ℚ)) + 2 * C := by
  classical
  have hpoint :=
    Finset.sum_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset ι)) ↦ square_le_mass_add_tail (K := K) (hN a))
  have hsum :
    (∑ a : ι, ∑ k ∈ Finset.Ico K P, if k < N a then 2 * (k : ℚ) + 1 else 0) =
      ∑ k ∈ Finset.Ico K P,
        (2 * (k : ℚ) + 1) * (Finset.univ.filter (fun a ↦ k + 1 ≤ N a)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_filter]
    simp only [← Nat.succ_le_iff, Finset.sum_const, nsmul_eq_mul, Nat.succ_eq_add_one]
    ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at hpoint
  have htailSum :
    (∑ k ∈ Finset.Ico K P, (2 * (k : ℚ) + 1) * (Finset.univ.filter (fun a ↦ k + 1 ≤ N a)).card) ≤
      2 * C / (K : ℚ) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico K P, 2 * (C : ℚ) * (1 / (k : ℚ) - 1 / ((k : ℚ) + 1)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact cubic_tail_term_le (hK.trans_le (Finset.mem_Ico.mp hk).1) (htail k hk)
      _ = 2 * C * (1 / (K : ℚ) - 1 / (P : ℚ)) := by
        rw [← Finset.mul_sum]
        have he := Finset.sum_Ico_sub (fun k ↦ -(1 / (k : ℚ))) hKP
        simp only [Nat.cast_add, Nat.cast_one, neg_sub_neg] at he
        rw [he]
      _ ≤ _ := by
        have hP : (0 : ℚ) ≤ 1 / (P : ℚ) := div_nonneg (by decide) (Nat.cast_nonneg P)
        have hCq : (0 : ℚ) ≤ 2 * C := mul_nonneg (by decide) (Nat.cast_nonneg C)
        rw [mul_sub, mul_one_div]
        exact sub_le_self _ (mul_nonneg hCq hP)
  have hkq : (0 : ℚ) < K := Nat.cast_pos.mpr hK
  have he := mul_le_mul_of_nonneg_left (hpoint.trans (add_le_add_right htailSum _)) hkq.le
  have hid : (K : ℚ) * (2 * C / (K : ℚ)) = 2 * C := by field_simp [ne_of_gt hkq]
  nlinarith only [he, hid]

end PseudoPrime.Analysis
