/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.LLS.PaperStatements.TriangularSignedZeroMass

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- For a nonprincipal character, the alpha-18 completed right integral equals
the negative scale-one arithmetic sum plus the gamma integral. Split the regular
logarithmic derivative and integrate its two integrable components.
This replaces a norm estimate by an exact arithmetic identity. -/
theorem triangular18_completed_rightIntegral_eq_arithmetic_add_gamma {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      -(∑' n : ℕ, K.summand χ 1 n) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let A := fun t : ℝ ↦
    -logDeriv χ.LFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let G := fun t : ℝ ↦
    logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have ha :=
    MellinKernel.integrable_arithmeticMellin_logDeriv K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at ha
  have hg :=
    MellinKernel.integrable_gammaFactor_power_line K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hg
  change MeasureTheory.Integrable A at ha
  change MeasureTheory.Integrable G at hg
  have he (t : ℝ) :
    logDeriv χ.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      -A t + G t := by
    let s : ℂ := (((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2
    have hz : s = ((17 / 16 : ℝ) : ℂ) + Complex.I * t := by
      dsimp only [s]
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hr : 1 ≤ s.re := by
      rw [hz]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      norm_num only
    have hp : 0 < s.re := zero_lt_one.trans_le hr
    have hd :=
      logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
        (AnalyticNumberTheory.DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hne hr)
        (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hp)
        (AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ
            hp).differentiableAt
    dsimp only [A, G]
    change logDeriv χ.completedLFunction s * _ = _
    rw [hd]
    ring
  have hs :=
    MellinKernel.tsum_summand_eq_integral_logDeriv K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hs
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ =
      -(∑' n : ℕ, K.summand χ 1 n) + ((1 / (2 * Real.pi) : ℝ) : ℂ) * _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_add (f := fun t : ℝ ↦ -A t) (g := G) ha.neg hg,
    MeasureTheory.integral_neg, mul_add]
  rw [hs]
  exact congrArg (fun z : ℂ ↦ z + ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, G t)) (mul_neg _ _)

end PseudoPrime.LLS.PaperStatements
