/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Finite dyadic covers for nonnegative integer weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Every positive v≤P lies in a band 2^j≤v≤2·2^j with j<log₂(P)+1.
Choose j=log₂(v) and use its exact power bounds. Closed upper endpoints
are allowed because later estimates only need a covering. -/
theorem exists_dyadic_band {v P : ℕ} (hv : 0 < v) (hP : v ≤ P) :
    ∃ j < Nat.log2 P + 1, 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j := by
  refine ⟨Nat.log2 v, ?_, Nat.log2_self_le hv.ne', ?_⟩
  · exact
      Nat.lt_succ_of_le
        ((Nat.le_log2 (hv.trans_le hP).ne').mpr ((Nat.log2_self_le hv.ne').trans hP))
  · have h := Nat.lt_log2_self (n := v)
    rw [Nat.pow_succ] at h
    exact h.le.trans_eq (Nat.mul_comm _ _)

/-- The square of v≤P is bounded by the sum of its dyadic band contributions.
Zero contributes zero; a positive v has at least one covering band, whose
summand equals v². All other summands are nonnegative. -/
theorem square_le_sum_dyadic_bands {v P : ℕ} (hP : v ≤ P) :
    v ^ 2 ≤
      ∑ j ∈ Finset.range (Nat.log2 P + 1), if 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j then v ^ 2 else 0 := by
  by_cases hv : v = 0
  · rw [hv]
    exact Nat.zero_le _
  obtain ⟨j, hj, hlo, hhi⟩ := exists_dyadic_band (Nat.pos_of_ne_zero hv) hP
  calc
    _ = if 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j then v ^ 2 else 0 := (ite_eq_left ⟨hlo, hhi⟩).symm
    _ ≤ _ :=
      Finset.single_le_sum (a := j) (f := fun k ↦ if 2 ^ k ≤ v ∧ v ≤ 2 * 2 ^ k then v ^ 2 else 0)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hj)

/-- Squares of a finite natural-valued family bounded by P are covered by
its dyadic level sums with log₂(P)+1 bands. Apply the pointwise covering and
interchange finite sums. This generic lemma supplies the full mixed-energy
reduction without enumeration of input integers or residue elements. -/
theorem sum_squares_le_sum_dyadic_bands {ι : Type*} (S : Finset ι) (r : ι → ℕ) (P : ℕ)
    (hr : ∀ x ∈ S, r x ≤ P) :
    (∑ x ∈ S, r x ^ 2) ≤
      ∑ j ∈ Finset.range (Nat.log2 P + 1),
        ∑ x ∈ S.filter (fun x ↦ 2 ^ j ≤ r x ∧ r x ≤ 2 * 2 ^ j), r x ^ 2 := by
  have h := Finset.sum_le_sum (fun x hx ↦ square_le_sum_dyadic_bands (hr x hx))
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_filter]

end PseudoPrime.Analysis
