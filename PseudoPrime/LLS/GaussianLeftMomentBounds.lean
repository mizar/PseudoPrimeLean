/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianArchimedeanBounds
public import PseudoPrime.LLS.GammaLeftMomentBounds

/-! # Explicit Gaussian left-contour moment bounds

The actual Gaussian integrand is bounded by 11/10 times the certified Gamma
moment envelope. Integrating the pointwise comparison retains the full power decay.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At the fixed left line -9/16 and positive scale, the actual Gaussian integrand
is at most 11/10 times the zeroth and first Gamma moment envelope. Factor the
Gaussian multiplier before applying the completed-derivative and Gamma estimates. -/
theorem gaussian_left_integrand_bound_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖-logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))‖ ≤
      (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) *
        ((Real.log q + 283) * Analysis.gammaLeftZeroEnvelope t +
          Analysis.gammaLeftFirstEnvelope t) := by
  have h :=
    gaussian_kernel_integrand_norm_le (-9 / 16) t
      (-logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2))
      ((x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hb := h.trans (mul_le_mul_of_nonneg_right gaussian_left_multiplier_le (norm_nonneg _))
  have hg :=
    mul_le_mul_of_nonneg_left (gamma_left_integrand_bound_moments hp hne hinv hx t)
      (by norm_num only : (0 : ℝ) ≤ 11 / 10)
  exact hb.trans (hg.trans_eq (by ring))

/-- For primitive nonprincipal data, nonprincipal inverse and positive scale,
the actual normalized Gaussian left integral is at most (11/10)x^(-9/16) times
(16/5)(log q+283)+5/3. Integrate the actual pointwise moment envelope and retain
its conductor dependence and full real-power decay. No RH assumption is needed. -/
theorem norm_gaussian_left_integral_le_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      ((11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
        (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hfi : MeasureTheory.Integrable F :=
    MellinKernel.integrable_completed_left_line gaussianGammaMellinKernel hp hne hinv
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) hx
  let C := Real.log q + 283
  let E := fun t : ℝ ↦
    ((11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)) *
      (C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t)
  have hgi : MeasureTheory.Integrable E :=
    ((Analysis.gammaLeftZeroEnvelope_integrable.const_mul C).add
          Analysis.gammaLeftFirstEnvelope_integrable).const_mul
      _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [Real.log_nonneg hq1]
  have hb :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gaussian_left_integrand_bound_moments hp hne hinv hx t))
  have hnorm := gamma_left_envelope_normalized_le hC
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hpi.le)]
  have hmul := mul_le_mul_of_nonneg_left hb (div_nonneg zero_le_one hpi.le)
  dsimp only [E] at hmul
  rw [MeasureTheory.integral_const_mul] at hmul
  calc
    _ ≤
        (1 / (2 * Real.pi)) *
          (((11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)) *
            (∫ t : ℝ, C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t)) :=
      hmul
    _ =
        ((11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)) *
          ((1 / (2 * Real.pi)) *
            (∫ t : ℝ, C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t)) :=
      by ring
    _ ≤ ((11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ)) * ((16 / 5) * C + 5 / 3) :=
      mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 11 / 10) (Real.rpow_nonneg hx.le _))

end PseudoPrime.LLS.PaperStatements
