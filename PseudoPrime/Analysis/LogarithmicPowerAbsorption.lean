/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerAsymptotics

/-! # Absorb fixed powers of one plus the logarithm -/

public section

namespace PseudoPrime.Analysis

/-- For a nonnegative coefficient and a positive power saving, a fixed natural
power of `1 + log x` is eventually smaller than that saving. Compare it with
`(2 * log x)^m` once `log x ≥ 1`, and use logarithmic little-o. This absorbs
the logarithmic factor in the thirteenth Heilbronn energy bound. -/
theorem eventually_mul_one_add_log_pow_lt_rpow {C s : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (m : ℕ) :
    ∀ᶠ x : ℝ in Filter.atTop, C * (1 + Real.log x) ^ m < x ^ s := by
  have h :=
    ((isLittleO_log_rpow_rpow_atTop (m : ℝ) hs).const_mul_left (C * 2 ^ m)).bound
      (by norm_num only : (0 : ℝ) < 1 / 2)
  filter_upwards [h, Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ)] with x hx hlog hx1
  rw [Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg (mul_nonneg hC (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) m))
        (pow_nonneg (zero_le_one.trans hlog) m)),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) s)] at hx
  have hpow :=
    pow_le_pow_left₀ (by linarith only [hlog] : 0 ≤ 1 + Real.log x)
      (by linarith only [hlog] : 1 + Real.log x ≤ 2 * Real.log x) m
  have hm := mul_le_mul_of_nonneg_left hpow hC
  rw [mul_pow] at hm
  have hpos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hx1) s
  nlinarith only [hm, hx, hpos]

end PseudoPrime.Analysis
