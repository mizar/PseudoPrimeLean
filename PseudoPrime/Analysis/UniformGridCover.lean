/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic

/-! # Closed uniform grid coverage -/

public section

namespace PseudoPrime.Analysis

/-- A point above the initial endpoint and below the previous grid endpoint
forces a positive cell count. The zero-count case contradicts the lower bound. -/
private theorem grid_count_pos {a h x : ℝ} {n : ℕ} (ha : a ≤ x) (hx : ¬a + (n : ℝ) * h ≤ x) :
    0 < n := by
  by_contra hn
  have hz := Nat.eq_zero_of_not_pos hn
  subst n
  simp only [Nat.cast_zero, zero_mul, add_zero] at hx
  exact hx ha

/-- A positive number of uniform closed cells covers every point between the outer endpoints.
Induction assigns a boundary point to a cell without using floor or list indexing.
The hypotheses contain both endpoint comparisons; the right endpoint is included. -/
theorem uniform_grid_cover (a h : ℝ) (n : ℕ) :
    0 < n →
      ∀ x : ℝ,
        a ≤ x →
          x ≤ a + (n : ℝ) * h →
          ∃ i : Fin n, a + (i.val : ℝ) * h ≤ x ∧ x ≤ a + ((i.val : ℝ) + 1) * h := by
  induction n with
  | zero =>
    intro hn; exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
    intro _ x ha hb
    by_cases hx : a + (n : ℝ) * h ≤ x
    · refine ⟨⟨n, Nat.lt_succ_self n⟩, hx, ?_⟩
      simpa only [Nat.cast_succ] using hb
    · obtain ⟨i, hi⟩ := ih (grid_count_pos ha hx) x ha (lt_of_not_ge hx).le
      exact ⟨i.castSucc, hi⟩

/-- A proposition follows from its proof on every uniform closed cell containing the point.
Select a covering cell and apply the supplied finite family of implications.
This transfers numerical cell certificates to a whole interval. -/
theorem uniform_grid_elim {a h x : ℝ} {n : ℕ} {P : Prop} (hn : 0 < n) (ha : a ≤ x)
    (hb : x ≤ a + (n : ℝ) * h)
    (hc : ∀ i : Fin n, a + (i.val : ℝ) * h ≤ x → x ≤ a + ((i.val : ℝ) + 1) * h → P) : P := by
  obtain ⟨i, hi⟩ := uniform_grid_cover a h n hn x ha hb
  exact hc i hi.1 hi.2

end PseudoPrime.Analysis
