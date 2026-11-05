/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleCumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourComparison

/-! # Strict improvement of the preceding full public selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- In the stated interval the preceding full selection equals its 0.4228 candidate.
Use the earlier factorial comparison to identify the remaining mean branch. -/
theorem reducedSelected_eq_mean_window {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 20000000) : reducedSelected n = (1057 / 2500 : ℝ) * Real.log n ^ 2 := by
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hm := meanSelected_lt_factorial hL hU
  rw [meanSelected, ite_eq_left h80] at hm
  have hf : (427 / 1000 : ℝ) * Real.log n ^ 2 < factorialSelected n := by
    exact (min_lt_iff.mp hm).resolve_left (lt_irrefl _)
  have he : meanSelected n = (427 / 1000 : ℝ) * Real.log n ^ 2 := by
    rw [meanSelected, ite_eq_left h80, min_eq_right hf.le]
  have hold : fixedImprovedSelected n = (427 / 1000 : ℝ) * Real.log n ^ 2 := by
    rw [fixedImproved_eq_mean_before_triangular (by linarith only [hU]), he]
  have hr : reducedSeriesCoeff (Real.log n) = 1057 / 2500 := by
    unfold reducedSeriesCoeff
    rw [ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU])]
  rw [reducedSelected, ite_eq_left h80, hold, hr, min_eq_right]
  nlinarith only [hs]

/-- On the stated nonempty scale interval the dual selection strictly improves
the entire preceding public selection, using the certified 0.4 witness. -/
theorem dualSelected_lt_reduced_window {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 14000000) : dualSelected n < reducedSelected n := by
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h81 : (81000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h5 : (5000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hold := reducedSelected_eq_mean_window hL (by linarith only [hU])
  have hr : dualMeanSeriesCoeff (Real.log n) ≤ 2 / 5 := by
    rw [dualMeanSeriesCoeff, ite_eq_left h81]
    apply (min_le_left _ _).trans
    rw [dualSeriesCoeff, ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU]), ite_eq_left h5]
  rw [dualSelected, ite_eq_left h80]
  apply (min_le_right _ _).trans_lt
  rw [hold]
  have hh := mul_le_mul_of_nonneg_right hr (le_of_lt hs)
  nlinarith only [hh, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
