/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic.Linarith

/-! # Finite centered errors with signed coefficients -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- An absolute centered error bound gives an upper bound after multiplication by
any real coefficient, including negative coefficients. Bound the signed error by its
absolute value, then multiply the supplied error bound by the coefficient's absolute value. -/
theorem signed_centered_term_le {b P m R : ℝ} (h : |P - m| ≤ R) : b * P ≤ b * m + |b| * R := by
  have hb := mul_le_mul_of_nonneg_left h (abs_nonneg b)
  have he := le_abs_self (b * (P - m))
  rw [abs_mul] at he
  nlinarith only [hb, he]

/-- For a finite list of centered quantities, signed coefficients multiply the common
main term with their signs intact, while their absolute values multiply the error bounds.
Sum the termwise comparison and distribute the two finite sums. This avoids an invalid
termwise upper-bound substitution at negative coefficients. -/
theorem sum_signed_centered_le {ι : Type} (l : List ι) (b P R : ι → ℝ) (m : ℝ)
    (h : ∀ i ∈ l, |P i - m| ≤ R i) :
    (l.map (fun i ↦ b i * P i)).sum ≤ (l.map b).sum * m + (l.map (fun i ↦ |b i| * R i)).sum := by
  have ht := List.sum_le_sum (fun i hi ↦ signed_centered_term_le (b := b i) (h i hi))
  rw [List.sum_map_add, List.sum_map_mul_right] at ht
  exact ht

end PseudoPrime.Analysis
