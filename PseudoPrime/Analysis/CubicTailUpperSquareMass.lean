/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CubicTailMoments

/-! # Log-free upper square mass from a uniform cubic distribution tail -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A square above M is its base square plus odd layers from M to n.
Extend layers to any upper bound P with zero terms. Below M both sides
vanish. This exact identity is summed before applying the cubic tail. -/
theorem upper_square_eq_base_add_layers {n M P : ℕ} (hn : n ≤ P) :
    (if M < n then (n : ℚ) ^ 2 else 0) =
      (if M < n then (M : ℚ) ^ 2 else 0) +
        ∑ k ∈ Finset.Ico M P, if k < n then 2 * (k : ℚ) + 1 else 0 := by
  by_cases h : M < n
  · rw [ite_eq_left h, ite_eq_left h]
    have he :
      (∑ k ∈ Finset.Ico M n, (2 * (k : ℚ) + 1)) =
        ∑ k ∈ Finset.Ico M P, if k < n then 2 * (k : ℚ) + 1 else 0 := by
      calc
        _ = ∑ k ∈ Finset.Ico M n, if k < n then 2 * (k : ℚ) + 1 else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          exact (ite_eq_left (Finset.mem_Ico.mp hk).2).symm
        _ = _ := by
          apply Finset.sum_subset (Finset.Ico_subset_Ico le_rfl hn)
          intro k hk hnot
          exact ite_eq_right (fun hlt ↦ hnot (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hk).1, hlt⟩))
    rw [← he, sum_odd_Ico_rat h.le]
    ring
  · rw [ite_eq_right h, ite_eq_right h, zero_add]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (fun hlt ↦ h (lt_of_le_of_lt (Finset.mem_Ico.mp hk).1 hlt))

/-- A cubic threshold bound controls the odd-layer sum above positive M
by 2C/M. Use the existing pointwise reciprocal bound and telescope.
The statement accepts any finite sample set. -/
theorem cubic_tail_odd_layers_le {ι : Type*} (S : Finset ι) (N : ι → ℕ) {P M C : ℕ} (hM : 0 < M)
    (hMP : M ≤ P)
    (ht : ∀ k ∈ Finset.Ico M P, (S.filter (fun x ↦ k + 1 ≤ N x)).card * (k + 1) ^ 3 ≤ C) :
    (∑ k ∈ Finset.Ico M P, (2 * (k : ℚ) + 1) * (S.filter (fun x ↦ k + 1 ≤ N x)).card) ≤
      2 * C / (M : ℚ) := by
  classical
    calc
    _ ≤ ∑ k ∈ Finset.Ico M P, 2 * (C : ℚ) * (1 / (k : ℚ) - 1 / ((k : ℚ) + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact cubic_tail_term_le (hM.trans_le (Finset.mem_Ico.mp hk).1) (ht k hk)
    _ = 2 * C * (1 / (M : ℚ) - 1 / (P : ℚ)) := by
      rw [← Finset.mul_sum]
      have he := Finset.sum_Ico_sub (fun k ↦ -(1 / (k : ℚ))) hMP
      simp only [Nat.cast_add, Nat.cast_one, neg_sub_neg] at he
      rw [he]
    _ ≤ _ := by
      have hP : (0 : ℚ) ≤ 1 / (P : ℚ) := div_nonneg (by decide) (Nat.cast_nonneg P)
      have hC : (0 : ℚ) ≤ 2 * C := mul_nonneg (by decide) (Nat.cast_nonneg C)
      rw [mul_sub, mul_one_div]
      exact sub_le_self _ (mul_nonneg hC hP)

/-- A finite natural family with cubic threshold count at most C has
upper square mass at most 3C/M for every positive M. Isolate the base
threshold and telescope all higher layers. This removes logarithmic loss. -/
theorem upper_square_mass_mul_le_of_cubic_tail {ι : Type*} (S : Finset ι) (N : ι → ℕ) (P C M : ℕ)
    (hN : ∀ x ∈ S, N x ≤ P) (hM : 0 < M)
    (ht : ∀ K : ℕ, 0 < K → (S.filter (fun x ↦ K ≤ N x)).card * K ^ 3 ≤ C) :
    M * (∑ x ∈ S.filter (fun x ↦ M < N x), N x ^ 2) ≤ 3 * C := by
  classical
  by_cases hMP : M ≤ P
  · have hpoint :=
      Finset.sum_congr rfl (fun x hx ↦ upper_square_eq_base_add_layers (M := M) (hN x hx))
    have hlayers :
      (∑ x ∈ S, ∑ k ∈ Finset.Ico M P, if k < N x then 2 * (k : ℚ) + 1 else 0) =
        ∑ k ∈ Finset.Ico M P, (2 * (k : ℚ) + 1) * (S.filter (fun x ↦ k + 1 ≤ N x)).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      simp only [← Nat.succ_le_iff, Finset.sum_const, nsmul_eq_mul, Nat.succ_eq_add_one]
      ring
    rw [← Finset.sum_filter, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, hlayers] at hpoint
    have hbase : (M : ℚ) ^ 3 * (S.filter (fun x ↦ M < N x)).card ≤ C := by
      have he : S.filter (fun x ↦ M < N x) = S.filter (fun x ↦ M + 1 ≤ N x) := by
        ext x
        simp only [Finset.mem_filter, Nat.lt_iff_add_one_le]
      rw [he]
      have hb :=
        (Nat.mul_le_mul_left (S.filter (fun x ↦ M + 1 ≤ N x)).card
              (Nat.pow_le_pow_left (Nat.le_succ M) 3)).trans
          (ht (M + 1) (Nat.succ_pos M))
      exact_mod_cast (Nat.mul_comm (M ^ 3) _).trans_le hb
    have hl := cubic_tail_odd_layers_le S N hM hMP (fun k _ ↦ ht (k + 1) (Nat.succ_pos k))
    have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg M : (0 : ℚ) ≤ M)
    have hd : (M : ℚ) * (2 * C / (M : ℚ)) = 2 * C := by
      field_simp [ne_of_gt (Nat.cast_pos.mpr hM : (0 : ℚ) < M)]
    have hf : (M : ℚ) * (∑ x ∈ S.filter (fun x ↦ M < N x), (N x : ℚ) ^ 2) ≤ 3 * C := by
      nlinarith only [hpoint, hbase, hm, hd]
    exact_mod_cast hf
  · have he : S.filter (fun x ↦ M < N x) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx hlt
      exact (Nat.lt_of_not_ge hMP).not_ge ((hlt.trans_le (hN x hx)).le)
    rw [he, Finset.sum_empty, mul_zero]
    exact Nat.zero_le _

end PseudoPrime.Analysis
