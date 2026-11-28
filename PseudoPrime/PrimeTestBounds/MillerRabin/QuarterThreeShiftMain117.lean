/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaMass101
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Main and zeta terms for the section 117 phase comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive radius with log n = 2r, the shifted real main term consists
of its conductor density and two poles. Factor out the common exponential. -/
theorem three_shift_real_main_eq (n : ℕ) {r h : ℝ} (hr : 0 < r) (hh : h ≤ 2 * Real.log r)
    (hn : Real.log n = 2 * r) :
    twoShiftRealMain n (r ^ 2 * Real.exp (-(14 / 5 + h))) =
      ((51 / 50 : ℝ) ^ 5 / 30) * Real.exp (-(13 / 25) * (2 * Real.log r)) *
          Real.exp ((51 / 50) * h) *
          (2 * Real.log r - h) ^ 5 -
        (3 * (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6) * Real.exp (h / 2) / r -
        (3 * (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6) * Real.exp (-(h / 2)) * r := by
  rw [twoShift_main_at_shift n hr hh, hn]
  have he :
    Real.exp (-(51 / 50 : ℝ) * (2 * Real.log r - h)) =
      Real.exp (-(51 / 50) * (2 * Real.log r)) * Real.exp ((51 / 50) * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs :
    r * Real.exp (-(51 / 50 : ℝ) * (2 * Real.log r)) =
      Real.exp (-(13 / 25) * (2 * Real.log r)) := by
    nth_rw 1 [← Real.exp_log hr]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 30 * Real.exp ((51 / 50) * h) * (2 * Real.log r - h) ^ 5) * hs

/-- The seven cosine terms and three shifted oscillating terms have total
zeta cost below 0.00003249 by the common absolute sixth-pole mass. -/
theorem three_shift_zeta_lower (hRH : RiemannHypothesis) {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) :
    let Z := fun t : ℝ ↦ (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm t ρ).re
    let B := twoShiftXiContourValue
    (-0.00003249 : ℝ) ≤
      3 *
        (3.143 * (B (14 / 5) + Z x) - 3.124 * (B (141 / 50) + Z y) - 0.0374 * (B (39 / 10) + Z z) -
              ((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * B 0 +
            3.143 * 3.124 * B (1 / 50) +
            3.143 * 0.0374 * B (11 / 10) -
          3.124 * 0.0374 * B (27 / 25)) := by
  intro Z B
  have hm := section101_zeta_mass hRH
  have hb {s : ℝ} (hs : 0 ≤ s) := abs_le.mp ((weighted_xi_contour_abs hRH hs).trans hm)
  have ht {t : ℝ} (hs : 0 < t) := abs_le.mp ((weighted_zeta_osc_abs hRH hs).trans hm)
  dsimp only [Z, B]
  linarith only [(hb (s := (14 / 5)) (by norm_num only)).1,
    (hb (s := (141 / 50)) (by norm_num only)).2, (hb (s := (39 / 10)) (by norm_num only)).2,
    (hb (s := 0) (by norm_num only)).2, (hb (s := (1 / 50)) (by norm_num only)).1,
    (hb (s := (11 / 10)) (by norm_num only)).1, (hb (s := (27 / 25)) (by norm_num only)).2,
    (ht hx).1, (ht hy).2, (ht hz).2]

end PseudoPrime.PrimeTestBounds.MillerRabin
