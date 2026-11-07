/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! # Simultaneous signs of three local quadratic values -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For three local quadratic values, including zero at nonunits, the sum of
pairwise products is at least minus one. Exhaust the three values of each
argument. This supplies the pointwise sign bound for the coupled Euler sum. -/
theorem quadratic_pair_sum_ge_neg_one (a b c : ℝ) (ha : a = -1 ∨ a = 0 ∨ a = 1)
    (hb : b = -1 ∨ b = 0 ∨ b = 1) (hc : c = -1 ∨ c = 0 ∨ c = 1) : -1 ≤ a * b + a * c + b * c := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;>
    norm_num only

/-- A Jacobi value at any level, cast to the reals, is minus one, zero or one.
The integer trichotomy preserves zero at nonunits. This prepares the simultaneous
pair bound without any coprimality assumption on the input. -/
theorem jacobi_real_trichotomy (a : ℤ) (p : ℕ) :
    (jacobiSym a p : ℝ) = -1 ∨ (jacobiSym a p : ℝ) = 0 ∨ (jacobiSym a p : ℝ) = 1 :=
  (jacobiSym.trichotomy a p).elim (fun h ↦ Or.inr (Or.inl (by rw [h, Int.cast_zero])))
    (fun h ↦
      h.elim (fun h ↦ Or.inr (Or.inr (by rw [h, Int.cast_one])))
        (fun h ↦ Or.inl (by rw [h, Int.cast_neg, Int.cast_one])))

/-- For an arbitrary integer and three levels, the local Jacobi pair products
have sum at least minus one, including nonunits. Apply the real sign inequality
to the three actual Jacobi values. This is the sign input to the Euler bound. -/
theorem jacobi_pair_sum_ge_neg_one (a : ℤ) (p q r : ℕ) :
    -1 ≤
      (jacobiSym a p : ℝ) * jacobiSym a q + (jacobiSym a p : ℝ) * jacobiSym a r +
        (jacobiSym a q : ℝ) * jacobiSym a r :=
  quadratic_pair_sum_ge_neg_one _ _ _ (jacobi_real_trichotomy a p) (jacobi_real_trichotomy a q)
    (jacobi_real_trichotomy a r)

/-- At three nonzero levels, the sum of the Jacobi values at their pairwise
products is at least minus one. Multiplicativity transfers the local sign bound
without excluding integers divisible by a level. This feeds primitive pair characters. -/
theorem jacobi_product_sum_ge_neg_one (a : ℤ) (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] :
    (-1 : ℝ) ≤ (jacobiSym a (p * q) : ℝ) + jacobiSym a (p * r) + jacobiSym a (q * r) := by
  rw [jacobiSym.mul_right, jacobiSym.mul_right, jacobiSym.mul_right, Int.cast_mul, Int.cast_mul,
    Int.cast_mul]
  exact jacobi_pair_sum_ge_neg_one a p q r

/-- For a nonnegative common weight, the negative local pair contributions sum
to at most that weight, including nonunits. Multiply the simultaneous sign bound
and rearrange. This controls the Euler tail outside the certified prefix. -/
theorem jacobi_weighted_pair_sum_le (a : ℤ) (p q r : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    -(jacobiSym a p : ℝ) * jacobiSym a q * w - (jacobiSym a p : ℝ) * jacobiSym a r * w -
        (jacobiSym a q : ℝ) * jacobiSym a r * w ≤
      w := by
  have h := mul_le_mul_of_nonneg_right (jacobi_pair_sum_ge_neg_one a p q r) hw
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
