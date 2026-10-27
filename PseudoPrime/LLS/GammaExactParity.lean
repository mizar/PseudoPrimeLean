/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaArchimedeanRealSeries

/-! # Exact parity bases for the central Gamma factor -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- Every complex Dirichlet character has central Gamma base exactly one
quarter or three quarters. Even and odd parity give the respective alternatives,
and positive real parts exclude the poles in the logarithmic derivative.
This supplies the precise arguments needed for the final sign estimates. -/
theorem gamma_central_eq_complex_digamma_exact_parity {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      (b = 1 / 4 ∨ b = 3 / 4) ∧
        ∀ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) =
            (-Complex.log Real.pi + Complex.digamma ((b : ℂ) + Complex.I * (t / 2))) / 2 := by
  rcases χ.even_or_odd with hχ | hχ
  · refine ⟨1 / 4, Or.inl rfl, ?_⟩
    intro t
    have hz : (Complex.I * (t : ℂ) + 1 / 2) / 2 = ((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    have hp : 0 < ((Complex.I * (t : ℂ) + 1 / 2) / 2).re := by
      simp only [complex_div_two_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only [Complex.one_re]
    have he :=
      logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat hχ
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
    rw [he, hz]
    ring
  · refine ⟨3 / 4, Or.inr rfl, ?_⟩
    intro t
    have hz :
      ((Complex.I * (t : ℂ) + 1 / 2) + 1) / 2 = ((3 / 4 : ℝ) : ℂ) + Complex.I * (t / 2) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    have hp : 0 < (((Complex.I * (t : ℂ) + 1 / 2) + 1) / 2).re := by
      simp only [complex_div_two_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only [Complex.one_re]
    have he :=
      logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat hχ
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
    rw [he, hz]
    ring

end PseudoPrime.LLS.PaperStatements
