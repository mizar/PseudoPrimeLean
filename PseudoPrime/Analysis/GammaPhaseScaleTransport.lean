/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaHalfHeightResolvent
public import PseudoPrime.Analysis.RationalPhaseTaylor

/-! # Logarithmic-scale transport of the actual Gamma phase -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At positive real scale, the imaginary complex power equals its unit
phase with angle t*log(x). Expand complex power and the real logarithm embedding. -/
theorem imaginary_power_eq_phase {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ (Complex.I * t) = Complex.exp (Complex.I * ((t * Real.log x : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
    Complex.ofReal_mul]
  congr 1
  ring

/-- At positive scales x and y, the Gamma phase difference has norm at most
2*|log(x)-log(y)|/(1+t^2). Apply the unit-phase Lipschitz bound and the certified
height-weighted Gamma envelope. This transports spectral comparisons between scales. -/
theorem gammaHalf_phase_scale_norm_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t) -
          Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)‖ ≤
      (2 / (1 + t ^ 2)) * |Real.log x - Real.log y| := by
  rw [← mul_sub, norm_mul, imaginary_power_eq_phase hx, imaginary_power_eq_phase hy]
  have hu := norm_phase_exp_sub_le (t * Real.log x) (t * Real.log y)
  rw [← mul_sub, abs_mul] at hu
  have hm :=
    mul_le_mul_of_nonneg_left hu (norm_nonneg (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)))
  have hg :=
    mul_le_mul_of_nonneg_right (gammaHalf_height_le_two_resolvent t)
      (abs_nonneg (Real.log x - Real.log y))
  exact hm.trans (by nlinarith only [hg])

/-- The negative real Gamma phase at a positive scale x is at most its
value at a positive anchor y plus the logarithmic scale error. Bound the difference
of real parts by the complex norm. This preserves the one-sided spectral comparison. -/
theorem gammaHalf_negative_phase_le_at_scale_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re +
        (2 / (1 + t ^ 2)) * |Real.log x - Real.log y| := by
  have h :=
    Complex.re_le_norm
      (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t) -
        Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  rw [Complex.sub_re, norm_sub_rev] at h
  have hb := gammaHalf_phase_scale_norm_sub_le hx hy t
  linarith only [h, hb]

end PseudoPrime.Analysis
