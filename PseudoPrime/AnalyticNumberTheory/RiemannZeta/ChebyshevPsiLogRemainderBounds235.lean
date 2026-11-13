/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogRemainder235
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # Explicit remainder bound at logarithmic scale 23.5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Given the displayed bounds on `L`, `a`, `c`, and `δ`, the zero-budget
remainder is at most `δ` times the displayed quadratic polynomial. Each
coefficient is bounded using `3 < π` and `δ ≤ 1/100`. -/
private theorem poly_bound {L a c δ : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (haL : a ≤ L / 2) (hc : 0 ≤ c)
    (hc2 : c ≤ 2) (hd : 0 ≤ δ) (hd1 : δ ≤ 1 / 100) :
    δ * a ^ 2 / (4 * Real.pi) + 53 / 100 * δ / 2 + δ * (a + 1) / Real.pi +
        δ * (1 + δ) / 2 * ((3 / 2 : ℝ) * (a + c) + 271 / 40) +
        δ ^ 2 * (1 + δ) / 6 ≤
      δ * (L ^ 2 / 48 + 3 * L / 5 + 6) := by
  have hsqa : a ^ 2 ≤ L ^ 2 / 4 := by
    have h :=
      mul_nonneg (show 0 ≤ L / 2 - a by linarith only [haL])
        (show 0 ≤ L / 2 + a by linarith only [hL, ha])
    nlinarith only [h]
  have hsqL := sq_nonneg L
  have hp := Real.pi_gt_three
  have hp4 : 0 < 4 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have h1 : a ^ 2 / (4 * Real.pi) ≤ L ^ 2 / 48 := by
    apply (div_le_iff₀ hp4).2
    have hm := mul_nonneg hsqL (sub_nonneg.mpr hp.le)
    nlinarith only [hsqa, hm]
  have h2 : (a + 1) / Real.pi ≤ L / 6 + 1 / 3 := by
    apply (div_le_iff₀ Real.pi_pos).2
    have hm := mul_nonneg (show 0 ≤ L + 2 by linarith only [hL]) (sub_nonneg.mpr hp.le)
    nlinarith only [haL, hm]
  let B := (3 / 2 : ℝ) * (a + c) + 271 / 40
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    linarith only [ha, hc]
  have hB : B ≤ 3 * L / 4 + 391 / 40 := by
    dsimp only [B]
    linarith only [haL, hc2]
  have hfac : (1 + δ) / 2 ≤ (101 / 200 : ℝ) := by linarith only [hd1]
  have hBprod := mul_le_mul hfac hB hB0 (by norm_num only : (0 : ℝ) ≤ 101 / 200)
  have hdquad : δ * (1 + δ) / 6 ≤ (101 / 60000 : ℝ) := by
    have hm := mul_nonneg hd (sub_nonneg.mpr hd1)
    nlinarith only [hm, hd1]
  have hcoef :
    a ^ 2 / (4 * Real.pi) + 53 / 200 + (a + 1) / Real.pi + (1 + δ) / 2 * B + δ * (1 + δ) / 6 ≤
      L ^ 2 / 48 + 3 * L / 5 + 6 := by
    nlinarith only [h1, h2, hBprod, hdquad, hL]
  have hm := mul_le_mul_of_nonneg_left hcoef hd
  dsimp only [B] at hm
  convert hm using 1
  ring

/-- On `L ≥ 47/2`, the selected cutoff logarithm lies between zero and `L/2`.
Logarithmic monotonicity and the square-root bound give the lower endpoint. -/
private theorem a_bounds {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    0 ≤ L / 2 - Real.log (5 * L / 6) ∧ L / 2 - Real.log (5 * L / 6) ≤ L / 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hx0 : 0 < 5 * L / 6 := by linarith only [hL]
  have hx1 : 1 ≤ 5 * L / 6 := by linarith only [hL]
  have hlog0 : 0 ≤ Real.log (5 * L / 6) := Real.log_nonneg hx1
  have hlogle : Real.log (5 * L / 6) ≤ Real.log L := Real.log_le_log hx0 (by linarith only [hL])
  have hlogs := PseudoPrime.Analysis.log_le_sqrt_of_pos hL0
  have hs := Real.sq_sqrt hL0.le
  have hs0 := Real.sqrt_nonneg L
  have hbound : Real.sqrt L ≤ L / 2 := by nlinarith only [hs, hs0, hL]
  constructor
  · linarith only [hlogle, hlogs, hbound]
  · linarith only [hlog0]

/-- For `L ≥ 47/2`, bound the relative width and the two inverse-scale
terms needed to compare the exact remainder with the cubic majorant. -/
private theorem simple_bounds {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let δ := 5 * L / (6 * Real.pi * s)
    let h := (5 * L / (6 * Real.pi)) * s
    δ ≤ (5 * L / 18) / s ∧ Real.log (2 * Real.pi) / s + 1 / (h * s) ≤ 3 / s := by
  dsimp only
  let s := Real.exp (L / 2)
  let δ := 5 * L / (6 * Real.pi * s)
  let h := (5 * L / (6 * Real.pi)) * s
  change δ ≤ (5 * L / 18) / s ∧ Real.log (2 * Real.pi) / s + 1 / (h * s) ≤ 3 / s
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : 1 ≤ s := by
    have he := exp_half_lower_235 hL
    change 5000 * L ≤ s at he
    linarith only [he, hL]
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  have hden : 18 * s ≤ 6 * Real.pi * s := by
    have hm := mul_le_mul_of_nonneg_right hp.le hs0.le
    linarith only [hm]
  have hdelta : δ ≤ (5 * L / 18) / s := by
    change 5 * L / (6 * Real.pi * s) ≤ _
    have hden0 : 0 < 18 * s := mul_pos (by norm_num only) hs0
    have h := div_le_div_of_nonneg_left (show 0 ≤ 5 * L by linarith only [hL0]) hden0 hden
    convert h using 1
    ring
  have hq : 1 ≤ 5 * L / (6 * Real.pi) := by
    apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [hL, hp4]
  have hh : 1 ≤ h := by
    change 1 ≤ (5 * L / (6 * Real.pi)) * s
    nlinarith only [hq, hs1, mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hs1)]
  have hinv : 1 / h ≤ 1 := (div_le_one₀ (by linarith only [hh])).2 hh
  have hc : Real.log (2 * Real.pi) ≤ 2 := by
    have := PseudoPrime.Analysis.log_two_mul_pi_lt
    linarith only [this]
  have hsum : Real.log (2 * Real.pi) + 1 / h ≤ 3 := by linarith only [hc, hinv]
  have hquot := div_le_div_of_nonneg_right hsum hs0.le
  have heq : (Real.log (2 * Real.pi) + 1 / h) / s = Real.log (2 * Real.pi) / s + 1 / (h * s) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact
    ⟨hdelta, by
      rw [heq] at hquot; exact hquot⟩

/-- For `L ≥ 47/2`, the exact normalized remainder of the sharp Chebyshev
estimate is at most `1/500`. The polynomial bound is combined with the
certified cubic-over-exponential estimate. -/
theorem scale235_remainder_le {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    let δ := 5 * L / (6 * Real.pi * Real.exp (L / 2))
    let h := (5 * L / (6 * Real.pi)) * Real.exp (L / 2)
    let a := L / 2 - Real.log (5 * L / 6)
    let c := Real.log (2 * Real.pi)
    δ * a ^ 2 / (4 * Real.pi) + 53 / 100 * δ / 2 + δ * (a + 1) / Real.pi +
        δ * (1 + δ) / 2 * ((3 / 2 : ℝ) * (a + c) + 271 / 40) +
        δ ^ 2 * (1 + δ) / 6 +
        c / Real.exp (L / 2) +
        1 / (h * Real.exp (L / 2)) ≤
      1 / 500 := by
  dsimp only
  let s := Real.exp (L / 2)
  let δ := 5 * L / (6 * Real.pi * s)
  let h := (5 * L / (6 * Real.pi)) * s
  let a := L / 2 - Real.log (5 * L / 6)
  let c := Real.log (2 * Real.pi)
  change
    δ * a ^ 2 / (4 * Real.pi) + 53 / 100 * δ / 2 + δ * (a + 1) / Real.pi +
        δ * (1 + δ) / 2 * ((3 / 2 : ℝ) * (a + c) + 271 / 40) +
        δ ^ 2 * (1 + δ) / 6 +
        c / s +
        1 / (h * s) ≤
      1 / 500
  have hL0 : 0 ≤ L := by linarith only [hL]
  have ha := a_bounds hL
  change 0 ≤ a ∧ a ≤ L / 2 at ha
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    linarith only [PseudoPrime.Analysis.log_two_mul_pi_gt]
  have hc2 : c ≤ 2 := by
    dsimp only [c]
    linarith only [PseudoPrime.Analysis.log_two_mul_pi_lt]
  have hd := scale235_conditions hL
  change 0 < δ ∧ δ ≤ 1 / 1000 ∧ 0 < h ∧ 1 < Real.exp L - h ∧ 2000 ≤ 12 * Real.pi * s / (5 * L) at hd
  have hd1 : δ ≤ 1 / 100 := by linarith only [hd.2.1]
  have hpoly := poly_bound hL0 ha.1 ha.2 hc0 hc2 hd.1.le hd1
  have hs := simple_bounds hL
  change δ ≤ (5 * L / 18) / s ∧ c / s + 1 / (h * s) ≤ 3 / s at hs
  have hp : 0 ≤ L ^ 2 / 48 + 3 * L / 5 + 6 := by nlinarith only [sq_nonneg L, hL0]
  have hmul := mul_le_mul_of_nonneg_right hs.1 hp
  have hr := scale235_cubic_remainder_le hL
  change (5 * L / 18 * (L ^ 2 / 48 + 3 * L / 5 + 6) + 3) / s ≤ 1 / 500 at hr
  have heq :
    (5 * L / 18) / s * (L ^ 2 / 48 + 3 * L / 5 + 6) + 3 / s =
      (5 * L / 18 * (L ^ 2 / 48 + 3 * L / 5 + 6) + 3) / s := by
    simp only [div_eq_mul_inv]
    ring
  linarith only [hpoly, hs.2, hmul, hr, heq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
