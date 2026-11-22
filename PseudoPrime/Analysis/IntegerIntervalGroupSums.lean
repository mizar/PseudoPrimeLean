/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalFiniteSums
import Mathlib.Tactic.Linarith

/-! # Combining independent group bounds -/

public section

namespace PseudoPrime.Analysis

/-- Pairwise disjoint groups with scaled lower and upper bounds also bound their union.
The resulting union can be used as one group in a subsequent aggregation without exposing the
individual group certificates. -/
theorem group_union_bounds {ι κ : Type*} [DecidableEq ι] (B : Finset κ) (A : κ → Finset ι)
    (hd : (↑B : Set κ).PairwiseDisjoint A) (v : ι → ℝ) (G : ℤ) (lo hi : κ → ℤ)
    (h : ∀ j ∈ B, (lo j : ℝ) ≤ G * ∑ i ∈ A j, v i ∧ G * ∑ i ∈ A j, v i ≤ (hi j : ℝ)) :
    ((∑ j ∈ B, lo j : ℤ) : ℝ) ≤ G * ∑ i ∈ B.biUnion A, v i ∧
      G * ∑ i ∈ B.biUnion A, v i ≤ ((∑ j ∈ B, hi j : ℤ) : ℝ) := by
  rw [Finset.sum_biUnion hd, Finset.mul_sum, Int.cast_sum, Int.cast_sum]
  exact ⟨Finset.sum_le_sum (fun j hj ↦ (h j hj).1), Finset.sum_le_sum (fun j hj ↦ (h j hj).2)⟩

/-- Disjoint checked groups and interval bounds for the remaining terms yield bounds for the full
sum. The endpoint sums can be checked independently from the groups, so the group proofs need not
expose their candidate tables or depend on one another. -/
theorem grouped_sum_bounds {ι κ : Type*} [Fintype ι] [DecidableEq ι] (B : Finset κ)
    (A : κ → Finset ι) (T : Finset ι) (hdisjoint : (↑B : Set κ).PairwiseDisjoint A)
    (hrestdisjoint : Disjoint (B.biUnion A) T) (hcover : B.biUnion A ∪ T = Finset.univ) (v : ι → ℝ)
    (R : ι → IntegerInterval) (G lo hi : ℤ) (lower upper : κ → ℤ) (hG : 0 < G)
    (hgroups : ∀ j ∈ B, (lower j : ℝ) ≤ G * (∑ i ∈ A j, v i) ∧ G * (∑ i ∈ A j, v i) ≤ (upper j : ℝ))
    (hrest : ∀ i ∈ T, (R i).Contains G (v i)) (hl : lo ≤ (∑ j ∈ B, lower j) + ∑ i ∈ T, (R i).lower)
    (hu : (∑ j ∈ B, upper j) + (∑ i ∈ T, (R i).upper) ≤ hi) :
    (lo : ℝ) ≤ G * (∑ i, v i) ∧ G * (∑ i, v i) ≤ (hi : ℝ) := by
  have hsplit : (∑ i, v i) = (∑ j ∈ B, ∑ i ∈ A j, v i) + ∑ i ∈ T, v i := by
    have h := Finset.sum_union (f := v) hrestdisjoint
    rw [hcover, Finset.sum_biUnion hdisjoint] at h
    exact h
  have hgroup := group_union_bounds B A hdisjoint v G lower upper hgroups
  rw [Finset.sum_biUnion hdisjoint] at hgroup
  have hlow := hgroup.1
  have hhigh := hgroup.2
  have htail := finite_sum_explicit_contains T R v G hrest
  have hp : (0 : ℝ) < G := by exact_mod_cast hG
  change
    ((∑ i ∈ T, (R i).lower : ℤ) : ℝ) / G ≤ ∑ i ∈ T, v i ∧
      (∑ i ∈ T, v i) ≤ ((∑ i ∈ T, (R i).upper : ℤ) : ℝ) / G at htail
  have htaillow := (div_le_iff₀ hp).mp htail.1
  have htailhigh := (le_div_iff₀ hp).mp htail.2
  have hl' : (lo : ℝ) ≤ (((∑ j ∈ B, lower j) + ∑ i ∈ T, (R i).lower : ℤ) : ℝ) := by
    exact_mod_cast hl
  have hu' : (((∑ j ∈ B, upper j) + ∑ i ∈ T, (R i).upper : ℤ) : ℝ) ≤ (hi : ℝ) := by
    exact_mod_cast hu
  rw [Int.cast_add] at hl' hu'
  rw [hsplit]
  constructor <;> nlinarith only [hlow, hhigh, htaillow, htailhigh, hl', hu']

end PseudoPrime.Analysis
