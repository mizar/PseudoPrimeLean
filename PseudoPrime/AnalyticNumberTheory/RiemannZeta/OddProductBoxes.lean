/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicEM8Intervals
public import Mathlib.Data.Nat.Prime.Defs

/-! # Odd rectangles computed from direct terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute a rectangle by multiplying the rectangles at the least factor and its quotient.
When that factorization does not decrease both arguments, use the direct rectangle.
Only the direct lookup and the rounding scale are supplied by the endpoint certificate. -/
def oddProductBox (G : ℤ) (direct : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval)
    (n : ℕ) : Analysis.IntegerInterval × Analysis.IntegerInterval :=
  let a := n.minFac
  let b := n / a
  if _h : a < n ∧ b < n then
    Analysis.roundedComplexProduct G (oddProductBox G direct a) (oddProductBox G direct b)
  else direct n
termination_by n
decreasing_by
  · exact _h.1
  · exact _h.2

/-- A prime argument uses its direct rectangle. -/
theorem oddProductBox_prime (G : ℤ)
    (direct : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) {n : ℕ} (hp : n.Prime) :
    oddProductBox G direct n = direct n := by
  rw [oddProductBox, dite_eq_right]
  exact fun h ↦ (Nat.not_lt_of_ge hp.minFac_eq.ge) h.1

/-- The unit argument uses its direct rectangle. -/
theorem oddProductBox_one (G : ℤ)
    (direct : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) :
    oddProductBox G direct 1 = direct 1 := by
  rw [oddProductBox, dite_eq_right]
  exact fun h ↦ (Nat.not_lt_of_ge Nat.minFac_one.ge) h.1

/-- When both factors are smaller, the rectangle is their rounded product. -/
theorem oddProductBox_factor (G : ℤ)
    (direct : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval) {n : ℕ} (ha : n.minFac < n)
    (hb : n / n.minFac < n) :
    oddProductBox G direct n =
      Analysis.roundedComplexProduct G (oddProductBox G direct n.minFac)
        (oddProductBox G direct (n / n.minFac)) := by
  rw [oddProductBox, dite_eq_left ⟨ha, hb⟩]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
