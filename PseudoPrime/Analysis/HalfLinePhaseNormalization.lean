/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RoundedEulerProduct

/-! # Combining half-line powers with imaginary phases -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: positive real bases a and x and any real ordinate.
Claim: the half-line power times the imaginary phase equals sqrt(a) times one exponential
with argument i*t*log(a*x). Proof: split the complex power and combine positive bases.
Role: isolate a single phase interval in finite Gamma node certification. -/
theorem halfLine_cpow_mul_phase {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (t : ℝ) :
    (a : ℂ) ^ ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t) =
      (Real.sqrt a : ℂ) * Complex.exp (Complex.I * ((t * Real.log (a * x) : ℝ) : ℂ)) := by
  have hhalf : (a : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt a : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), hhalf, mul_assoc, ←
    Complex.mul_cpow_ofReal_nonneg ha.le hx.le, ← Complex.ofReal_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ha hx).ne'), ←
    Complex.ofReal_log (mul_pos ha hx).le, Complex.ofReal_mul]
  congr 2
  ring

end PseudoPrime.Analysis
