/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularMellin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit quadratic decay of the alpha-18 kernel on fixed contour lines

The nonzero real coordinate avoids the compactness bound near the origin.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On either fixed line abs(Re s)=9/16, the alpha-18 triangular Mellin
function has norm at most 10^12/(1+Im(s)^2). Bound both exponentials by exp(11),
cancel the nonzero denominator, and use the certified exp(1)<3 estimate.
This replaces the existential strip-decay constant in the triangular integrals. -/
theorem triangular18_fixed_line_decay {s : ℂ} (hs : |s.re| = (9 / 16 : ℝ)) :
    ‖triangularMellinFunction 18 s‖ ≤ (1000000000000 : ℝ) / (1 + s.im ^ 2) := by
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re, abs_zero] at hs
    norm_num only at hs
  have hre : -(9 / 16 : ℝ) ≤ s.re ∧ s.re ≤ 9 / 16 := abs_le.mp hs.le
  have h1 : ‖Complex.exp (((18 : ℝ) : ℂ) * s)‖ ≤ Real.exp 11 := by
    rw [Complex.norm_exp, Complex.mul_re]
    norm_num only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Real.exp_le_exp.mpr (by linarith only [hre.2])
  have h2 : ‖Complex.exp (-(((18 : ℝ) : ℂ) * s))‖ ≤ Real.exp 11 := by
    rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re]
    norm_num only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Real.exp_le_exp.mpr (by linarith only [hre.1])
  have hN :=
    (norm_sub_le (Complex.exp (((18 : ℝ) : ℂ) * s)) (Complex.exp (-(((18 : ℝ) : ℂ) * s)))).trans
      (add_le_add h1 h2)
  have hc :
    ‖triangularMellinFunction 18 s‖ * ‖s‖ ^ 2 =
      ‖Complex.exp (((18 : ℝ) : ℂ) * s) - Complex.exp (-(((18 : ℝ) : ℂ) * s))‖ ^ 2 := by
    rw [triangularMellinFunction_of_ne_zero (by norm_num only : (18 : ℝ) ≠ 0) hs0, norm_pow,
      norm_div, ← mul_pow, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hs0)]
  have hsq : s.re ^ 2 = (9 / 16 : ℝ) ^ 2 := by rw [← sq_abs s.re, hs]
  have hnorm := Complex.sq_norm s
  rw [Complex.normSq_apply] at hnorm
  have hscale : (81 / 256 : ℝ) * (1 + s.im ^ 2) ≤ ‖s‖ ^ 2 := by
    nlinarith only [hnorm, hsq, sq_nonneg s.im]
  have hm := mul_le_mul_of_nonneg_left hscale (norm_nonneg (triangularMellinFunction 18 s))
  rw [hc] at hm
  have he : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
  have he22 := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide : (22 : ℕ) ≠ 0)
  have h11 : Real.exp 11 ^ 2 = Real.exp 1 ^ 22 := by
    rw [pow_two, ← Real.exp_add, show (11 : ℝ) + 11 = 22 by norm_num only]
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 22
  have hnum : (4 : ℝ) * 3 ^ 22 < (81 / 256 : ℝ) * 1000000000000 := by norm_num only
  apply (le_div_iff₀ (by linarith only [sq_nonneg s.im] : 0 < 1 + s.im ^ 2)).mpr
  have hNsq :=
    mul_self_le_mul_self
      (norm_nonneg (Complex.exp (((18 : ℝ) : ℂ) * s) - Complex.exp (-(((18 : ℝ) : ℂ) * s)))) hN
  nlinarith only [hm, hNsq, h11, he22, hnum]

end PseudoPrime.Analysis
