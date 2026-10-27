/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Laplace representation of the central digamma resolvent -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive real part, the central resolvent is the integral of its
decaying exponential on the positive half-line. This representation supplies
the denominator factor for the Gamma inverse Mellin calculation. -/
theorem central_resolvent_eq_laplace {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (1 : ℂ) / ((c : ℂ) + Complex.I * (t : ℂ) / 2) =
      ∫ r : ℝ in Set.Ioi 0, Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ)) := by
  have hn : (-((c : ℂ) + Complex.I * (t : ℂ) / 2)).re < 0 := by
    simpa only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      zero_div, add_zero] using neg_neg_of_pos hc
  rw [integral_exp_mul_complex_Ioi hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]

/-- The decaying exponential in the central resolvent representation is
integrable on the positive half-line whenever its real parameter is positive.
This is the one-variable integrability input for the later Fubini argument. -/
theorem integrableOn_central_resolvent_laplace {c : ℝ} (hc : 0 < c) (t : ℝ) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => Complex.exp (-((c : ℂ) + Complex.I * (t : ℂ) / 2) * (r : ℂ))) (Set.Ioi 0) := by
  have hn : (-((c : ℂ) + Complex.I * (t : ℂ) / 2)).re < 0 := by
    simpa only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      zero_div, add_zero] using neg_neg_of_pos hc
  exact integrableOn_exp_mul_complex_Ioi hn 0

end PseudoPrime.LLS.PaperStatements
