/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularZeroMassFormula

/-! # Exact conductor coefficient in the alpha-18 triangular zero formula

Reflect the completed logarithmic derivative and integrate the isolated conductor.
The leading coefficient is exactly 36; reflected terms remain to be bounded.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The normalized alpha-18 kernel integral on the left line -9/16 equals
36. Evaluate the inverse Mellin transform at one using the proved line-independent
triangular inversion. This is the exact conductor coefficient in the zero formula. -/
theorem triangular18_left_kernelIntegral :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      36 := by
  have hi :=
    inverseMellin_triangular (by norm_num only : (0 : ℝ) < 18)
      (by norm_num only : |(-9 / 16 : ℝ)| ≤ 1) (by norm_num only : (0 : ℝ) < 1)
  simp only [inverseMellin, Complex.ofReal_one, Complex.one_cpow, mul_one, triangularKernelProfile,
    Real.log_one, abs_zero, sub_zero] at hi
  norm_num only at hi
  simpa only [max_eq_right (by norm_num only : (0 : ℝ) ≤ 36), Complex.ofReal_ofNat, neg_div] using
    hi

/-- For primitive nonprincipal data with nonprincipal inverse, reflect the
completed logarithmic derivative on the line with real part -1/16. The right
line has real part 17/16 and the exact conductor contribution is log(q).
This is the pointwise decomposition of the alpha-18 left integrand. -/
theorem triangular18_completed_left_reflection {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (t : ℝ) :
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) =
      Complex.log q + logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) := by
  have hr : 1 ≤ (((17 / 16 : ℝ) : ℂ) - Complex.I * t).re := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    norm_num only
  have he :=
    AnalyticNumberTheory.DirichletLFunction.completedLFunction_logDeriv_functionalEquation_at hp hne
      (AnalyticNumberTheory.DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hs :
    (1 : ℂ) - (((17 / 16 : ℝ) : ℂ) - Complex.I * t) =
      (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
    ring
  rw [hs] at he
  exact he

/-- For primitive nonprincipal data and nonprincipal inverse, the normalized
alpha-18 completed left integral equals 36*log(q) plus the reflected inverse
logarithmic-derivative integral. Prove integrability of the difference, split the
integral using the functional equation, and evaluate the kernel's integral.
This identifies the conductor coefficient without an asymptotic or mass assumption. -/
theorem triangular18_left_completedIntegral_eq_conductor_add_reflected {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      36 * Complex.log q +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let C := fun t : ℝ ↦ Complex.log q * K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let R := fun t : ℝ ↦
    logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
      K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hF : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16) (x := 1)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only)
    simpa only [Complex.ofReal_one, Complex.one_cpow, mul_one] using hi
  have hC : MeasureTheory.Integrable C :=
    (MellinKernel.integrable_line_in_strip K (c := -9 / 16)
          (by
            change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
          (by
            change (-9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
          (by norm_num only)).const_mul
      _
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R]
    rw [triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (Filter.Eventually.of_forall (fun t ↦ by rw [Pi.sub_apply, he t, add_sub_cancel_left]))
  have hsum : (∫ t : ℝ, F t) = (∫ t : ℝ, C t) + (∫ t : ℝ, R t) := by
    rw [← MeasureTheory.integral_add hC hR]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hsum, mul_add]
  have hconst : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, C t) = 36 * Complex.log q := by
    rw [show
        C =
          (fun t : ℝ ↦
            Complex.log q *
              Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
        from rfl,
      MeasureTheory.integral_const_mul]
    calc
      _ =
          Complex.log q *
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) :=
        by ring
      _ = _ := by rw [triangular18_left_kernelIntegral, mul_comm]
  rw [hconst]

/-- Under primitive nonprincipal GRH data, the scale-one arithmetic sum plus
the alpha-18 absolute zero mass equals the exact leading conductor term
36*log(q), the pole, and two conductor-free reflected/gamma integrands.
Insert the proved left-line decomposition into the positive zero-mass formula.
The remaining terms require explicit bounds to obtain the additive constant. -/
theorem triangular18_absoluteMass_conductor_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' n : ℕ, K.summand χ 1 n) + ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      36 * Complex.log q +
        MellinKernel.weightedResidue K (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) 1 (-1 / 2) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv (DirichletCharacter.gammaFactor χ)
                (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  have he := triangular18_absoluteMass_explicit_formula hq hGRH hp hne hinv
  dsimp only at he ⊢
  rw [triangular18_left_completedIntegral_eq_conductor_add_reflected hp hne hinv] at he
  linear_combination he

end PseudoPrime.LLS.PaperStatements
