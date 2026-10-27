/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianMellinAverage
public import PseudoPrime.LLS.GammaSignedLeftIntegral
public import PseudoPrime.LLS.GaussianLeftMomentBounds

/-! # Gaussian averaging of the signed Gamma left integral

The fixed Gaussian multiplier on the left contour is the logarithmic Gaussian
average of the signed, unsmoothed Gamma left integral at rescaled arguments.
This identity lets a real-part estimate on the unsmoothed integral pass to the
Gaussian contour without replacing it by a norm bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Rescaling the positive argument of the unsmoothed signed left integrand
multiplies its Mellin term by `exp(sv)` on the line with real part `-9/16`.
The positive-base complex-power identity controls the branch exactly. This is
the pointwise scale relation used before averaging. -/
theorem gammaSignedLeftIntegrand_logScale {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {x : ℝ}
    (hx : 0 < x) (v t : ℝ) :
    gammaSignedLeftIntegrand χ (x * Real.exp v) t =
      Complex.exp ((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
        gammaSignedLeftIntegrand χ x t := by
  rw [gammaSignedLeftIntegrand, gammaSignedLeftIntegrand, gammaSignedLeftWeight,
    gammaSignedLeftWeight]
  have hc := gaussian_cpow_scale hx (-v) (-(((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)))
  have hv : (↑(-v) : ℂ) = -(v : ℂ) := by rw [Complex.ofReal_neg]
  rw [hv, neg_mul_neg, neg_neg, neg_neg] at hc
  have ht : Complex.I * (t : ℂ) = (t : ℂ) * Complex.I := by ring
  rw [ht] at hc
  rw [hc.symm]
  ring_nf

/-- Rescaling the argument of `gammaSignedLeftIntegral` inserts the vertical
Mellin exponential before its normalization. Integrate the pointwise scale
identity and retain the original factor `1/(2π)`. -/
theorem gammaSignedLeftIntegral_logScale {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {x : ℝ}
    (hx : 0 < x) (v : ℝ) :
    gammaSignedLeftIntegral χ (x * Real.exp v) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.exp ((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
            gammaSignedLeftIntegrand χ x t) := by
  rw [gammaSignedLeftIntegral]
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun t => gammaSignedLeftIntegrand_logScale hx v t

/-- Express the signed Gaussian left-contour integral as the normalized
logarithmic Gaussian average of `gammaSignedLeftIntegral` at `x * exp v`.
The generic Fubini transfer applies to the integrable unsmoothed integrand, and
the positive-base complex-power identity identifies its shifted scale. This
preserves the signed real-part estimate needed by the MR `B_6` argument. -/
theorem gaussian_signed_left_integral_eq_logGaussianAverage {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∫ v : ℝ,
        (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
          gammaSignedLeftIntegral χ (x * Real.exp v) := by
  let F : ℝ → ℂ := gammaSignedLeftIntegrand χ x
  have hF : MeasureTheory.Integrable F := integrable_gammaSignedLeftIntegrand hp hne hinv hx
  have hline (t : ℝ) :
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
        (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ))) =
      Complex.exp (((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) ^ 2) / 4) * F t := by
    let s : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)
    have harg : s + 1 / 2 = ((-1 / 16 : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
      dsimp only [s]
      push_cast
      ring
    change
      -logDeriv χ.completedLFunction (s + 1 / 2) *
          (PseudoPrime.Analysis.gaussianGammaFunction s * (x : ℂ) ^ s) =
        Complex.exp (s ^ 2 / 4) * gammaSignedLeftIntegrand χ x t
    rw [PseudoPrime.Analysis.gaussianGammaFunction, harg, gammaSignedLeftIntegrand,
      gammaSignedLeftWeight]
    dsimp only [s]
    ring_nf
  have hgauss :
    (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∫ t : ℝ, Complex.exp (((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) ^ 2) / 4) * F t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hline)
  calc
    _ =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, Complex.exp ((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) ^ 2 / 4) * F t) :=
      congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z) hgauss
    _ =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ,
            (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
              (∫ t : ℝ,
                Complex.exp ((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t)) :=
      congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
        (integral_gaussianMultiplier_eq_logGaussianAverage (c := -9 / 16) hF)
    _ =
        ∫ v : ℝ,
          (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
            gammaSignedLeftIntegral χ (x * Real.exp v) :=
      by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      exact
        Filter.Eventually.of_forall fun v => by
          change
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ((PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                  (∫ t : ℝ,
                    Complex.exp ((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t)) =
              (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
                gammaSignedLeftIntegral χ (x * Real.exp v)
          rw [gammaSignedLeftIntegral_logScale hx v]
          have hcast : ((1 / (2 * Real.pi) : ℝ) : ℂ) = (1 : ℂ) / ((2 * Real.pi : ℝ) : ℂ) := by
            rw [Complex.ofReal_div, Complex.ofReal_one]
          rw [hcast]
          ring

/-
The signed Gaussian left integral inherits the real-part estimate of the
unsmoothed contour after integrating against the positive normalized Gaussian.
-/
theorem re_gaussian_signed_left_integral_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (∫ v : ℝ,
          (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
            gammaSignedLeftIntegral χ (x * Real.exp v)).re ≤
      (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let G : ℝ → ℂ := fun v =>
    (PseudoPrime.Analysis.normalizedGaussianWeight v : ℂ) *
      gammaSignedLeftIntegral χ (x * Real.exp v)
  have hF : MeasureTheory.Integrable (gammaSignedLeftIntegrand χ x) :=
    integrable_gammaSignedLeftIntegrand hp hne hinv hx
  have hH := integrable_logGaussianAverage_integrand (c := -9 / 16) hF
  have hG : MeasureTheory.Integrable G := by
    apply (hH.const_mul ((1 / (2 * Real.pi) : ℝ) : ℂ)).congr
    filter_upwards with v
    dsimp only [G]
    rw [gammaSignedLeftIntegral_logScale hx v]
    have hInt :
      (∫ t : ℝ,
          Complex.exp ((((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
            gammaSignedLeftIntegrand χ x t) =
        ∫ t : ℝ,
          Complex.exp (((-9 / 16 : ℝ) : ℂ) * (v : ℂ) + Complex.I * (v : ℂ) * (t : ℂ)) *
            gammaSignedLeftIntegrand χ x t := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by ring_nf
    rw [hInt]
    ring_nf
  have hRe := Complex.reCLM.integrable_comp hG
  have hpoint (v : ℝ) :
    (G v).re ≤
      PseudoPrime.Analysis.normalizedGaussianWeight v *
        (43 * (x * Real.exp v) ^ (-9 / 16 : ℝ)) := by
    dsimp only [G]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact
      mul_le_mul_of_nonneg_left
        (re_gammaSignedLeftIntegral_le hp hne hinv (mul_pos hx (Real.exp_pos v)))
        (PseudoPrime.Analysis.normalizedGaussianWeight_pos v).le
  have hfactor (v : ℝ) :
    PseudoPrime.Analysis.normalizedGaussianWeight v * (43 * (x * Real.exp v) ^ (-9 / 16 : ℝ)) =
      (43 * x ^ (-9 / 16 : ℝ)) *
        (PseudoPrime.Analysis.normalizedGaussianWeight v * Real.exp ((-9 / 16 : ℝ) * v)) := by
    rw [Real.mul_rpow hx.le (Real.exp_pos v).le]
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos (Real.exp_pos v)]
    rw [Real.log_exp]
    ring_nf
  have hupper :
    MeasureTheory.Integrable
      (fun v : ℝ =>
        PseudoPrime.Analysis.normalizedGaussianWeight v *
          (43 * (x * Real.exp v) ^ (-9 / 16 : ℝ))) := by
    have hi :=
      (PseudoPrime.Analysis.integrable_normalizedGaussian_mul_exp (-9 / 16)).const_mul
        (43 * x ^ (-9 / 16 : ℝ))
    apply hi.congr
    filter_upwards with v
    exact (hfactor v).symm
  have hmono := MeasureTheory.integral_mono hRe hupper hpoint
  have he := Complex.reCLM.integral_comp_comm hG
  calc
    (∫ v : ℝ, G v).re = ∫ v : ℝ, (G v).re := he.symm
    _ ≤
        ∫ v : ℝ,
          PseudoPrime.Analysis.normalizedGaussianWeight v *
            (43 * (x * Real.exp v) ^ (-9 / 16 : ℝ)) :=
      hmono
    _ = (43 * x ^ (-9 / 16 : ℝ)) * Real.exp (((-9 / 16 : ℝ) ^ 2) / 4) := by
      calc
        _ =
            ∫ v : ℝ,
              (43 * x ^ (-9 / 16 : ℝ)) *
                (PseudoPrime.Analysis.normalizedGaussianWeight v * Real.exp ((-9 / 16 : ℝ) * v)) :=
          by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun v => hfactor v
        _ =
            (43 * x ^ (-9 / 16 : ℝ)) *
              ∫ v : ℝ,
                PseudoPrime.Analysis.normalizedGaussianWeight v * Real.exp ((-9 / 16 : ℝ) * v) :=
          MeasureTheory.integral_const_mul _ _
        _ = _ := by rw [PseudoPrime.Analysis.integral_normalizedGaussian_mul_exp]
    _ ≤ (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
      have he' := gaussian_left_multiplier_le
      have hxpow : 0 ≤ x ^ (-9 / 16 : ℝ) := Real.rpow_nonneg hx.le _
      have hm := mul_le_mul_of_nonneg_left he' (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 43) hxpow)
      norm_num only at hm ⊢
      nlinarith only [hm]

end PseudoPrime.LLS.PaperStatements
