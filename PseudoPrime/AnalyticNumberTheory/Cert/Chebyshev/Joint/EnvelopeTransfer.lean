/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PrimeTicks
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # From scalar logarithm ticks to the normalized Lee–Nosal estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- A checked integer tick gives a lower logarithm in thousandths at any positive input. -/
private theorem log_floor {n m : ℕ} (hn : n ≠ 0)
    (h : scale * m ≤ 1000 * (primeTicks gridTicks (gridTicks 32) n).1) :
    (m : ℝ) / 1000 ≤ Real.log n := by
  have hr : (scale : ℝ) * m ≤ 1000 * ((primeTicks gridTicks (gridTicks 32) n).1 : ℝ) := by
    exact_mod_cast h
  have hl := (primeTicks_sound hn).1
  norm_num only [scale, Nat.cast_pow, Nat.cast_ofNat] at hr hl
  linarith only [hr, hl]

/-- A tangent bound for log at eight transfers a scalar lower bound for log x
to a lower bound for the Lee–Nosal coefficient. -/
private theorem coefficient {x l c : ℝ} (hl : l ≤ Real.log x) (hpos : 2 ≤ l) (hc : 0 ≤ c)
    (hnum : 8 * (22 / 7) * c ≤ l * (7 / 8 * l - 27 / 25)) :
    c ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hL : 0 < Real.log x := by linarith only [hl, hpos]
  have ht := Real.log_le_sub_one_of_pos (show 0 < Real.log x / 8 by linarith only [hL])
  rw [Real.log_div hL.ne' (by norm_num only : (8 : ℝ) ≠ 0)] at ht
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 3 = 8 by norm_num only] using Real.log_pow 2 3
  have hgap : 7 / 8 * l - 27 / 25 ≤ Real.log x - Real.log (Real.log x) := by
    linarith only [hl, ht, h8, Real.log_two_lt_d9]
  have hm := mul_le_mul hl hgap (by linarith only [hpos]) hL.le
  apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
  have hπ := mul_le_mul_of_nonneg_right (show Real.pi ≤ 22 / 7 by linarith only [Real.pi_lt_d4]) hc
  linarith only [hπ, hnum, hm]

/-- The lower logarithm checked at the left endpoint transfers the coefficient bound to x. -/
theorem coefficient_from_ticks {n m : ℕ} {x c : ℝ} (hn : 0 < n) (hx : (n : ℝ) ≤ x)
    (ht : scale * m ≤ 1000 * (primeTicks gridTicks (gridTicks 32) n).1) (hm : (2 : ℝ) ≤ m / 1000)
    (hc : 0 ≤ c) (hnum : 8 * (22 / 7) * c ≤ (m / 1000 : ℝ) * (7 / 8 * (m / 1000 : ℝ) - 27 / 25)) :
    c ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact
    coefficient ((log_floor hn.ne' ht).trans (Real.log_le_log (Nat.cast_pos.mpr hn) hx)) hm hc hnum

/-- A coefficient comparison converts the absolute theta error to its normalized envelope. -/
theorem theta_ratio_of_coeff {x c : ℝ} (hx : 0 < x) (hθ : |Chebyshev.theta x - x| ≤ c * Real.sqrt x)
    (hc : c ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact ((div_le_iff₀ (Real.sqrt_pos.2 hx)).2 hθ).trans hc

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
