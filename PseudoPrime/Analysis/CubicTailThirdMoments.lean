/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CubicTailMoments
public import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Third moments from uniform cubic tails -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Cubes are bounded by the sum of three times the squared upper endpoints
of their unit layers. Induction compares consecutive cubes with that square.
This supplies a nonnegative layer representation for finite third moments. -/
theorem cube_le_sum_squared_layers (n : ℕ) :
    (n : ℚ) ^ 3 ≤ ∑ k ∈ Finset.range n, 3 * ((k : ℚ) + 1) ^ 2 := by
  induction n with
  | zero => norm_num only [Nat.cast_zero, zero_pow, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    nlinarith only [ih, (Nat.cast_nonneg n : (0 : ℚ) ≤ n)]

/-- A layer sum for n≤P extends to range P with zero terms above n.
Finite-sum inclusion proves the identity. This permits interchanging the
sample index with a common finite set of heights. -/
theorem sum_squared_layers_eq_extended {n P : ℕ} (hn : n ≤ P) :
    (∑ k ∈ Finset.range n, 3 * ((k : ℚ) + 1) ^ 2) =
      ∑ k ∈ Finset.range P, if k < n then 3 * ((k : ℚ) + 1) ^ 2 else 0 := by
  calc
    _ = ∑ k ∈ Finset.range n, if k < n then 3 * ((k : ℚ) + 1) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (ite_eq_left (Finset.mem_range.mp hk)).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono hn)
      intro k _ hnot
      exact ite_eq_right (fun h ↦ hnot (Finset.mem_range.mpr h))

/-- A cubic tail bound at positive height k+1 bounds its squared layer by
3C/(k+1). Cast the natural inequality and divide by the positive height.
The resulting harmonic majorant is summed in the third-moment estimate. -/
theorem cubic_tail_squared_layer_le {k H C : ℕ} (h : H * (k + 1) ^ 3 ≤ C) :
    3 * ((k : ℚ) + 1) ^ 2 * H ≤ 3 * C / ((k : ℚ) + 1) := by
  have hk : (0 : ℚ) < (k : ℚ) + 1 := by linarith only [(Nat.cast_nonneg k : (0 : ℚ) ≤ k)]
  apply (le_div_iff₀ hk).mpr
  have hc : (H : ℚ) * ((k : ℚ) + 1) ^ 3 ≤ C := by exact_mod_cast h
  nlinarith only [hc]

/-- A natural-valued finite family bounded by P with uniform cubic tail C
has third moment at most 3C times the Pth harmonic number. Sum the layer
majorant and interchange finite sums. No analytic distribution assumption
beyond the stated tail bound is introduced. -/
theorem sum_cubes_le_of_cubic_tail {ι : Type*} [Fintype ι] (N : ι → ℕ) (P C : ℕ) (hN : ∀ a, N a ≤ P)
    (htail :
      ∀ k ∈ Finset.range P, (Finset.univ.filter (fun a ↦ k + 1 ≤ N a)).card * (k + 1) ^ 3 ≤ C) :
    (∑ a, (N a : ℚ) ^ 3) ≤ 3 * C * harmonic P := by
  classical
  have hp :=
    Finset.sum_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset ι)) ↦
        (cube_le_sum_squared_layers (N a)).trans_eq (sum_squared_layers_eq_extended (hN a)))
  have he :
    (∑ a : ι, ∑ k ∈ Finset.range P, if k < N a then 3 * ((k : ℚ) + 1) ^ 2 else 0) =
      ∑ k ∈ Finset.range P,
        3 * ((k : ℚ) + 1) ^ 2 * (Finset.univ.filter (fun a ↦ k + 1 ≤ N a)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_filter]
    simp only [← Nat.succ_le_iff, Finset.sum_const, nsmul_eq_mul, Nat.succ_eq_add_one]
    ring
  rw [he] at hp
  calc
    _ ≤ _ := hp
    _ ≤ ∑ k ∈ Finset.range P, 3 * (C : ℚ) / ((k : ℚ) + 1) :=
      Finset.sum_le_sum (fun k hk ↦ cubic_tail_squared_layer_le (htail k hk))
    _ = _ := by
      unfold harmonic
      simp only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, Finset.mul_sum]

end PseudoPrime.Analysis
