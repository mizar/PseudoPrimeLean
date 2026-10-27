/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExcludedCharacterDefect
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuadraticAmbientSquares

/-! # Combined quadratic exclusion budgets with exact square cancellation -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For arbitrary real coefficients and weights, the excluded character
defect is linear in the weight. Distribute the finite sum without positivity
assumptions. This combines reciprocal and logarithmic costs before bounding. -/
theorem excludedCharacterDefect_linear_weight {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (S : Finset ℕ) (w v : ℕ → ℝ) (a b : ℝ) :
    excludedCharacterDefect χ N S (fun n ↦ a * w n + b * v n) =
      a * excludedCharacterDefect χ N S w + b * excludedCharacterDefect χ N S v := by
  unfold excludedCharacterDefect
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A character-independent quadratic exclusion budget on S: outside the
excluded support no term is charged; inside it, level nonunits have coefficient
one, level-unit squares coefficient zero and other level units coefficient two.
Nonnegative weights make this an upper budget for any quadratic character. -/
noncomputable def quadraticExcludedBudget (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n N),
    (if Nat.Coprime n q then if IsSquare n then 0 else 2 else 1) * w n

/-- For a quadratic character and nonnegative weights on S, the exact
excluded defect is at most the quadratic structural budget. Level nonunits
have value zero, unit squares value one, and other real parts are at least -1.
No primitivity, GRH or relation between q and N is required. -/
theorem excludedCharacterDefect_le_quadratic_budget {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) :
    excludedCharacterDefect χ N S w ≤ quadraticExcludedBudget q N S w := by
  apply Finset.sum_le_sum
  intro n hn
  have hw0 := hw n (Finset.mem_filter.mp hn).1
  by_cases hc : Nat.Coprime n q
  · rw [ite_eq_left hc]
    by_cases hs : IsSquare n
    · rw [ite_eq_left hs, quadratic_character_apply_one_of_coprime_square χ hquad hc hs,
        Complex.one_re, sub_self]
    · rw [ite_eq_right hs]
      have hr := (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))).1
      exact mul_le_mul_of_nonneg_right (by linarith only [hr]) hw0
  · rw [ite_eq_right hc]
    have hz : χ n = 0 := χ.map_nonunit (fun hu ↦ hc ((ZMod.isUnit_iff_coprime n q).mp hu))
    rw [hz, Complex.zero_re, sub_zero]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
