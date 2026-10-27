/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteTripleCorrelations
public import Mathlib.Tactic.Linarith

/-! # Truncating a natural-valued square mass using its third moment -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The second moment of a finite natural-valued family is at most its
third moment. Zero contributes zero and every positive integer is at
least one. This bounds the integer rounding cost of a moment cutoff. -/
theorem finite_square_mass_le_cube_mass {ι : Type*} (S : Finset ι) (r : ι → ℕ) :
    (∑ x ∈ S, r x ^ 2) ≤ ∑ x ∈ S, r x ^ 3 := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hz : r x = 0
  · simpa only [hz, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0)] using Nat.zero_le 0
  · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hz) (by decide : 2 ≤ 3)

/-- Above a height M, square mass times M is at most the full third moment.
Compare Mr² with r³ on the upper tail and enlarge its nonnegative sum.
This avoids a separate tail-count estimate in the energy truncation. -/
theorem finite_upper_square_tail_mul_le_cube_mass {ι : Type*} (S : Finset ι) (r : ι → ℕ) (M : ℕ) :
    M * (∑ x ∈ S.filter (fun x ↦ M < r x), r x ^ 2) ≤ ∑ x ∈ S, r x ^ 3 := by
  rw [Finset.mul_sum]
  apply
    (Finset.sum_le_sum (s := S.filter (fun x ↦ M < r x)) (fun x hx ↦ ?_)).trans
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ S))
  have h := Nat.mul_le_mul_right (r x ^ 2) (Finset.mem_filter.mp hx).2.le
  calc
    _ ≤ r x * r x ^ 2 := h
    _ = r x ^ 3 := by ring

/-- Positive E≤T admits an integer cutoff with 4T≤ME≤5T. Choose
M=floor(4T/E)+1. The exact integer division inequalities control rounding,
so the cutoff has the required E-dependent height without a real ceiling. -/
theorem exists_third_moment_cutoff {E T : ℕ} (hE : 0 < E) (hET : E ≤ T) :
    ∃ M : ℕ, 0 < M ∧ 4 * T ≤ M * E ∧ M * E ≤ 5 * T := by
  refine ⟨4 * T / E + 1, Nat.zero_lt_succ _, ?_, ?_⟩
  · exact (Nat.lt_mul_div_succ (4 * T) hE).le.trans_eq (Nat.mul_comm _ _)
  · have h := Nat.div_mul_le_self (4 * T) E
    nlinarith only [h, hET]

/-- If E=d+B+H, d≤E/4 and MH≤T≤ME/4, the lower part B retains at least
half of E. Work with multiplied natural inequalities and cancel the
positive cutoff M. This combines exact diagonal and upper-tail accounting. -/
theorem half_energy_le_of_third_moment_cutoff {E d B H T M : ℕ} (he : E = d + B + H)
    (hd : 4 * d ≤ E) (ht : M * H ≤ T) (hcap : 4 * T ≤ M * E) (hM : 0 < M) : E ≤ 2 * B := by
  have hde := Nat.mul_le_mul_left M hd
  have he' : M * E = M * d + M * B + M * H := by
    rw [he]; ring
  have hscaled : M * E ≤ M * (2 * B) := by nlinarith only [hde, he', ht, hcap]
  exact Nat.le_of_mul_le_mul_left hscaled hM

end PseudoPrime.Analysis
