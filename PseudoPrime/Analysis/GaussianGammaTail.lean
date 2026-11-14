/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaKernel
import PseudoPrime.Analysis.GammaCriticalLineTail

/-! # Explicit Gaussian Gamma tail bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At every real height, the Gaussian kernel norm is at most the unweighted
Gamma norm. The exact vertical-line identity and exp(-t²/4)≤1 preserve its tail estimate. -/
theorem norm_gaussianGammaFunction_le_Gamma (t : ℝ) :
    ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤
      ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  have h := norm_gaussianGammaFunction_vertical 0 t
  simp only [Complex.ofReal_zero, zero_add, zero_pow (by decide : 2 ≠ 0), zero_sub,
    add_comm (Complex.I * (t : ℂ)) (1 / 2)] at h
  have he : Real.exp (-(t ^ 2) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t])
  rw [h]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg _)

/-- For |t|≥16, the scaled Gaussian kernel norm is below 1/40000.
Apply Gaussian damping to the existing unweighted Gamma tail bound. -/
theorem scaled_gaussianGamma_lt_of_abs_ge_16 {t : ℝ} (ht : 16 ≤ |t|) :
    (1 + t ^ 2) * ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ < 1 / 40000 := by
  exact
    (mul_le_mul_of_nonneg_left (norm_gaussianGammaFunction_le_Gamma t)
          (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))).trans_lt
      (scaled_Gamma_half_add_I_lt_of_abs_ge_sixteen ht)

end PseudoPrime.Analysis
