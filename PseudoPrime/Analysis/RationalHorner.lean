/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.List.Forall2
public import Mathlib.Tactic

/-! # Positivity certificates for rational Horner polynomials -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: rational coefficients in ascending order and a real argument.
Output: their polynomial value, evaluated by Horner recursion with empty value zero.
Role: verify compact exact polynomial certificates without a large symbolic payload. -/
noncomputable def rationalHorner : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: l, v => (c : ℝ) + v * rationalHorner l v

/-- Input: nonnegative rational coefficients and a nonnegative real argument.
Claim: their Horner value is nonnegative.
Proof: induct on the list using positivity of each product and sum.
Role: certify whole-halfline polynomial inequalities. -/
theorem rationalHorner_nonneg (l : List ℚ) (hc : ∀ c ∈ l, 0 ≤ c) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ rationalHorner l v := by
  induction l with
  | nil => exact le_refl 0
  | cons a l ih =>
    exact
      add_nonneg (Rat.cast_nonneg.mpr (hc a List.mem_cons_self))
        (mul_nonneg hv (ih (fun b hb ↦ hc b (List.mem_cons_of_mem a hb))))

/-- Input: a nonempty rational coefficient list whose positivity check succeeds,
and a nonnegative real argument. Claim: its Horner value is strictly positive.
Proof: use the positive first coefficient and nonnegative remaining polynomial.
Role: turn exact coefficient checks into strict analytic comparisons. -/
theorem rationalHorner_pos_of_all (l : List ℚ) (hne : l ≠ [])
    (hc : l.all (fun c ↦ decide (0 < c)) = true) {v : ℝ} (hv : 0 ≤ v) : 0 < rationalHorner l v := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons a l =>
    have hp := List.all_eq_true.mp hc
    exact
      add_pos_of_pos_of_nonneg (Rat.cast_pos.mpr (of_decide_eq_true (hp a List.mem_cons_self)))
        (mul_nonneg hv
          (rationalHorner_nonneg l
            (fun b hb ↦ (of_decide_eq_true (hp b (List.mem_cons_of_mem a hb))).le) hv))

end PseudoPrime.Analysis
