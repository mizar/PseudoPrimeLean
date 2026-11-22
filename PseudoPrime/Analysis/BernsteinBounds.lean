/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Bounds from Bernstein coefficients -/

public section

namespace PseudoPrime.Analysis

/-- A Bernstein polynomial on the unit interval is bounded above by any common
upper bound for its coefficients. The nonnegative Bernstein basis has sum one,
so this applies to certificates of any degree, including the degree-twelve
polynomials used in finite Chebyshev estimates. -/
theorem bernstein_sum_le (n : ℕ) (c : Fin (n + 1) → ℝ) (t : Set.Icc (0 : ℝ) 1) (M : ℝ)
    (hc : ∀ k, c k ≤ M) : (∑ k : Fin (n + 1), c k * bernstein n k t) ≤ M := by
  calc
    _ ≤ ∑ k : Fin (n + 1), M * bernstein n k t := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hc k) bernstein_nonneg
    _ = M := by rw [← Finset.mul_sum, bernstein.probability, mul_one]

/-- A Bernstein polynomial on the unit interval is bounded below by any common
lower bound for its coefficients. This is the matching lower certificate for
finite interval estimates, obtained from nonnegativity and partition of unity. -/
theorem le_bernstein_sum (n : ℕ) (c : Fin (n + 1) → ℝ) (t : Set.Icc (0 : ℝ) 1) (m : ℝ)
    (hc : ∀ k, m ≤ c k) : m ≤ ∑ k : Fin (n + 1), c k * bernstein n k t := by
  calc
    m = ∑ k : Fin (n + 1), m * bernstein n k t := by
      rw [← Finset.mul_sum, bernstein.probability, mul_one]
    _ ≤ ∑ k : Fin (n + 1), c k * bernstein n k t := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hc k) bernstein_nonneg

/-- Every point of a nondegenerate closed interval has a coordinate in the
unit interval. This coordinate transfers Bernstein certificates to a cell. -/
theorem exists_unit_coord {a b x : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    ∃ t : Set.Icc (0 : ℝ) 1, x = a + (b - a) * (t : ℝ) := by
  let t : Set.Icc (0 : ℝ) 1 :=
    ⟨(x - a) / (b - a),
      ⟨div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hab.le),
        (div_le_one₀ (sub_pos.mpr hab)).2 (sub_le_sub_right hxb a)⟩⟩
  refine ⟨t, ?_⟩
  change x = a + (b - a) * ((x - a) / (b - a))
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab)), add_comm, sub_add_cancel]

/-- A Bernstein representation on a nondegenerate real interval is bounded
above by any common upper bound for its coefficients. The interval coordinate
reduces the result to `bernstein_sum_le`, so each cell can be checked separately. -/
theorem bernstein_interval_le {a b x : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) (f : ℝ → ℝ)
    (n : ℕ) (c : Fin (n + 1) → ℝ) (M : ℝ) (hc : ∀ i, c i ≤ M)
    (hrep :
      ∀ t : Set.Icc (0 : ℝ) 1,
        f (a + (b - a) * (t : ℝ)) = ∑ i : Fin (n + 1), c i * bernstein n i t) :
    f x ≤ M := by
  obtain ⟨t, rfl⟩ := exists_unit_coord hab hax hxb
  rw [hrep]
  exact bernstein_sum_le n c t M hc

end PseudoPrime.Analysis
