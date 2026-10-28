/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleGammaCharacterBounds
public import PseudoPrime.LLS.QuadraticExcludedBudget

/-! # Paired Euler savings with a combined quadratic exclusion budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For weights supported on Mangoldt indices below the prime-triviality cutoff,
the paired character sum equals twice the principal sum minus the exact excluded
defect. Rearrange the weighted defect identity without positivity assumptions. -/
theorem paired_weighted_sum_eq_of_ambient_trivial {q N : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ S, (1 + (χ n).re) * w n) = 2 * (∑ n ∈ S, w n) - excludedCharacterDefect χ N S w := by
  have he := weighted_defect_eq_excluded_of_ambient_trivial χ S w hS hw ht
  have hs : (∑ n ∈ S, (1 + (χ n).re) * w n) = (∑ n ∈ S, w n) + (∑ n ∈ S, (χ n).re * w n) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  linarith only [he, hs]

/-- For a quadratic character under prime triviality, nonnegative Mangoldt weights
give a paired-sum lower bound with the structural exclusion budget. Combine the
exact identity and square cancellation. No RH or primitivity is required. -/
theorem paired_weighted_sum_ge_quadratic_budget {q N : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, ArithmeticFunction.vonMangoldt n = 0 → w n = 0) (hw0 : ∀ n ∈ S, 0 ≤ w n)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    2 * (∑ n ∈ S, w n) - quadraticExcludedBudget q N S w ≤ (∑ n ∈ S, (1 + (χ n).re) * w n) := by
  rw [paired_weighted_sum_eq_of_ambient_trivial χ S w hS hw ht]
  exact sub_le_sub_left (excludedCharacterDefect_le_quadratic_budget χ hquad N S w hw0) _

end PseudoPrime.AnalyticNumberTheory.Arithmetic
