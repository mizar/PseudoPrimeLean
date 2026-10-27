/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianArchimedeanBounds
public import PseudoPrime.LLS.GammaPoleBounds

/-! # Explicit Gaussian kernel-pole contribution

The regularized coefficient at -1/2 is exp(1/16). Retain its rational allowance
2129/2000 in the ambient completed endpoint bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonprincipal character and positive scale, the Gaussian kernel-pole norm
is exp(1/16) times the completed logarithmic derivative norm at zero divided by
sqrt(x). Evaluate the actual regularized coefficient and the real power at the pole. -/
theorem gaussian_poleResidue_norm {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hne : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    ‖MellinKernel.weightedResidue gaussianGammaMellinKernel
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)‖ =
      Real.exp (1 / 16 : ℝ) * ‖logDeriv χ.completedLFunction 0‖ / Real.sqrt x := by
  have he : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  simp only [MellinKernel.weightedResidue, ite_true]
  rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_shifted_completed hne, he, norm_mul,
    norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hr : gaussianGammaMellinKernel.regularized (-1 / 2) = Complex.exp ((1 / 16 : ℝ) : ℂ) := by
    change Complex.Gamma (-1 / 2 + 1 / 2 + 1) * Complex.exp ((-1 / 2 : ℂ) ^ 2 / 4) = _
    rw [show (-1 / 2 : ℂ) + 1 / 2 + 1 = 1 by ring, Complex.Gamma_one, one_mul]
    congr 1
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hr, Complex.norm_exp]
  norm_num only [Complex.ofReal_re, Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  ring

/-- Under GRH for primitive nonprincipal conductor 3≤m≤q and ambient q≥20000,
the actual Gaussian pole contribution is at most 2129/2000 times the ambient
affine logarithmic endpoint bound divided by sqrt(x). Use the exact pole identity
and the proved exponential allowance, retaining small primitive conductors. -/
theorem gaussian_poleResidue_le_ambient {q m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    ‖MellinKernel.weightedResidue gaussianGammaMellinKernel
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)‖ ≤
      (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) := by
  rw [gaussian_poleResidue_norm hne hx]
  have h1 :=
    mul_le_mul_of_nonneg_right Analysis.gaussian_endpoint_exp_le
      (norm_nonneg (logDeriv χ.completedLFunction 0))
  have h2 :=
    mul_le_mul_of_nonneg_left
      (norm_completedLogDeriv_zero_le_ambient_affine_log hq hm hmq hp hne hGRH)
      (by norm_num only : (0 : ℝ) ≤ 2129 / 2000)
  exact (div_le_div_of_nonneg_right (h1.trans h2) (Real.sqrt_nonneg x)).trans_eq (by ring)

end PseudoPrime.LLS.PaperStatements
