/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularConductorFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogarithmicBounds
public import PseudoPrime.Analysis.TriangularFixedLineDecay

/-! # Logarithmic reflected and gamma integral bounds for the alpha-18 kernel

Explicit logarithmic constants replace nonintegrable linear-height majorants.
Kernel decay and the common logarithmic integral remain numerical inputs.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A complex logarithmic-growth factor and an inverse-square factor give
an integral norm bound A*B times the common finite logarithmic integral.
A is nonnegative; the pointwise bounds control both factors. Apply the Bochner
integral norm inequality with the proved integrable majorant.
This transfers explicit derivative constants to triangular remainder integrals. -/
theorem norm_logWeighted_product_integral_le {F G : ℝ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hF : ∀ t : ℝ, ‖F t‖ ≤ A * (Real.log (4 + |t|) + 1)) (hG : ∀ t : ℝ, ‖G t‖ ≤ B / (1 + t ^ 2)) :
    ‖∫ t : ℝ, F t * G t‖ ≤ (A * B) * (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
  have hi := Analysis.integrable_log_add_abs_div_one_add_sq.const_mul (A * B)
  have hb (t : ℝ) : ‖F t * G t‖ ≤ (A * B) * ((Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
    have hL : 0 ≤ Real.log (4 + |t|) + 1 :=
      add_nonneg (Real.log_nonneg (by linarith only [abs_nonneg t])) zero_le_one
    calc
      _ = ‖F t‖ * ‖G t‖ := norm_mul _ _
      _ ≤ (A * (Real.log (4 + |t|) + 1)) * (B / (1 + t ^ 2)) :=
        mul_le_mul (hF t) (hG t) (norm_nonneg _) (mul_nonneg hA hL)
      _ = _ := by ring
  have h := MeasureTheory.norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hb)
  rw [MeasureTheory.integral_const_mul] at h
  exact h

/-- The alpha-18 reflected inverse-character integral is bounded by 284*B
times the common logarithmic integral if its left-line kernel has decay
B/(1+t^2). Use the completed logarithmic derivative bound at reflected height.
This controls the conductor-free left remainder; B still needs numerical certification. -/
theorem triangular18_reflectedIntegral_norm_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hinv : χ⁻¹ ≠ 1) {B : ℝ}
    (hK :
      ∀ t : ℝ,
        ‖Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
          B / (1 + t ^ 2)) :
    ‖∫ t : ℝ,
          logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (284 * B) * (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
  apply norm_logWeighted_product_integral_le (by norm_num only : (0 : ℝ) ≤ 284) _ hK
  intro t
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_completed_seventeen_sixteenths_le_log hinv
      (-t)
  simp only [Complex.ofReal_neg, mul_neg, abs_neg, ← sub_eq_add_neg] at hb
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  linarith only [hb, hL]

/-- The alpha-18 gamma-factor integral is bounded by 12*B times the common
logarithmic integral if its right-line kernel has decay B/(1+t^2).
The gamma logarithmic derivative is evaluated at real part 17/16 for both
parities. This controls the gamma remainder; B still needs numerical certification. -/
theorem triangular18_gammaIntegral_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hK :
      ∀ t : ℝ,
        ‖Analysis.triangularMellinFunction 18 (((9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
          B / (1 + t ^ 2)) :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 18 (((9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (12 * B) * (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
  apply norm_logWeighted_product_integral_le (by norm_num only : (0 : ℝ) ≤ 12) _ hK
  intro t
  have hr : (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2).re = 17 / 16 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
    norm_num only
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_seventeen_sixteenths_le_log χ
      hr
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im, zero_div,
    add_zero] at hb
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  linarith only [hb, hL]

/-- The actual alpha-18 reflected integral is bounded by 284*10^12 times
the common finite logarithmic integral for a nonprincipal inverse character.
Insert the certified fixed-line decay into the reflected logarithmic bound.
No kernel decay constant remains as a hypothesis. -/
theorem triangular18_reflectedIntegral_norm_le_fixed_decay {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hinv : χ⁻¹ ≠ 1) :
    ‖∫ t : ℝ,
          logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (284 * 1000000000000 : ℝ) * (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
  apply triangular18_reflectedIntegral_norm_le hinv
  intro t
  have hs : |(((-9 / 16 : ℝ) : ℂ) + Complex.I * t).re| = (9 / 16 : ℝ) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only
  have hd := Analysis.triangular18_fixed_line_decay hs
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, one_mul, zero_mul, zero_add] using hd

/-- The actual alpha-18 gamma integral is bounded by 12*10^12 times the
common finite logarithmic integral for every character. Insert the certified
fixed-line decay into the gamma logarithmic bound. No supplied kernel bound
remains; the common integral still needs a numerical upper bound. -/
theorem triangular18_gammaIntegral_norm_le_fixed_decay {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 18 (((9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (12 * 1000000000000 : ℝ) * (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
  apply triangular18_gammaIntegral_norm_le χ
  intro t
  have hs : |(((9 / 16 : ℝ) : ℂ) + Complex.I * t).re| = (9 / 16 : ℝ) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only
  have hd := Analysis.triangular18_fixed_line_decay hs
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, one_mul, zero_mul, zero_add] using hd

end PseudoPrime.LLS.PaperStatements
