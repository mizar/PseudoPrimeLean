/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PositiveTaylorTransport
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Exact rational moments on arbitrary finite lists -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The exact kth weighted mass moment of a finite list.
The weight and mass are arbitrary rational functions; no sign assumptions
are imposed. Fixed row weights permit reuse at every target scale. -/
def gammaRationalListMoment {ι : Type*} (rows : List ι) (w m : ι → ℚ) (k : ℕ) : ℚ :=
  (rows.map (fun r ↦ w r * m r ^ k)).sum

/-- Input: arbitrary rational weight, mass, increment and Taylor term count.
Claim: a weighted Taylor atom equals its finite moment expansion.
Proof: distribute the finite sum and rearrange rational products.
This is the algebraic input for a fixed moment table. -/
theorem gamma_weighted_taylor_eq_moments (w m d : ℚ) (n : ℕ) :
    w * gammaPositiveTaylor (m * d) n =
      ∑ k ∈ Finset.range n, d ^ k / (k.factorial : ℚ) * (w * m ^ k) := by
  simp only [gammaPositiveTaylor, Finset.mul_sum, mul_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Input: any finite list and rational weight, mass and increment.
Claim: its Taylor sum equals a polynomial in the increment with exact moments.
Proof: apply the atom identity and interchange finite sums by induction.
No analytic moment bounds are subtracted in this identity. -/
theorem gamma_list_taylor_eq_moments {ι : Type*} (rows : List ι) (w m : ι → ℚ) (d : ℚ) (n : ℕ) :
    (rows.map (fun r ↦ w r * gammaPositiveTaylor (m r * d) n)).sum =
      ∑ k ∈ Finset.range n, d ^ k / (k.factorial : ℚ) * gammaRationalListMoment rows w m k := by
  induction rows with
  | nil =>
    simp only [List.map_nil, List.sum_nil, gammaRationalListMoment, mul_zero, Finset.sum_const_zero]
  | cons r rows
    ih =>
    simp only [List.map_cons, List.sum_cons, gammaRationalListMoment] at ih ⊢
    rw [gamma_weighted_taylor_eq_moments, ih]
    simp only [mul_add, Finset.sum_add_distrib]

/-- Input: an arbitrary finite list and two ordered rational thresholds.
Claim: the exact band moment is the difference of the two prefix moments.
Proof: split the upper prefix at the lower threshold.
This permits reuse of a fixed prefix-moment table as the support moves. -/
theorem gamma_list_band_moment_eq_prefix_sub {ι : Type*} (rows : List ι) (w m t : ι → ℚ) {a b : ℚ}
    (hab : a ≤ b) (k : ℕ) :
    gammaRationalListMoment (rows.filter (fun r ↦ decide (a < t r ∧ t r ≤ b))) w m k =
      gammaRationalListMoment (rows.filter (fun r ↦ decide (t r ≤ b))) w m k -
        gammaRationalListMoment (rows.filter (fun r ↦ decide (t r ≤ a))) w m k := by
  have hlo :
    (rows.filter (fun r ↦ decide (t r ≤ b))).filter (fun r ↦ decide (t r ≤ a)) =
      rows.filter (fun r ↦ decide (t r ≤ a)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.decide_iff]
    exact ⟨And.left, fun h ↦ ⟨h, h.trans hab⟩⟩
  have hmid :
    (rows.filter (fun r ↦ decide (t r ≤ b))).filter (fun r ↦ decide (¬t r ≤ a)) =
      rows.filter (fun r ↦ decide (a < t r ∧ t r ≤ b)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.decide_iff, not_le]
  have h :=
    List.sum_map_filter_add_sum_map_filter_not (fun r ↦ t r ≤ a) (fun r ↦ w r * m r ^ k)
      (rows.filter (fun r ↦ decide (t r ≤ b)))
  rw [hlo, hmid] at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [gammaRationalListMoment, add_comm] using h)

end PseudoPrime.Analysis
