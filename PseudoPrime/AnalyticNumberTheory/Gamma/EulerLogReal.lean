/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-! # Euler Gamma logarithm on the positive real axis -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

private theorem correction_im_ofReal {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (logCorrection k (x : ℂ)).im = 0 := by
  unfold logCorrection
  have h0 : 0 ≤ x + k := (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k)).le
  have h1 : 0 ≤ (k : ℝ) + 1 := add_nonneg (Nat.cast_nonneg k) zero_le_one
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_log h0, ← Complex.ofReal_log h1,
    ← Complex.ofReal_sub, Complex.ofReal_im]

/-- The Euler-normalized Gamma logarithm is real on the positive real axis.
Each correction term is real, and the summable series commutes with taking
imaginary parts. This fixes the Gamma phase at the Riemann–von Mangoldt base. -/
theorem logGammaSeries_im_ofReal {x : ℝ} (hx : 0 < x) : (logGammaSeries (x : ℂ)).im = 0 := by
  have hs :=
    (logCorrection_summable_and_deriv (s := (x : ℂ)) (by simpa only [Complex.ofReal_re] using hx)).1
  simp only [logGammaSeries, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_neg,
    ← Complex.ofReal_mul, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_tsum hs,
    correction_im_ofReal hx, tsum_zero]

end PseudoPrime.AnalyticNumberTheory.Gamma
