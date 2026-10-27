/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelPoleBounds
public import PseudoPrime.LLS.GammaKernel

/-! # Explicit Gamma kernel-pole contribution

The regularized Gamma pole has coefficient one. The completed endpoint bounds
therefore give explicit residue errors, including small primitive conductors.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonprincipal character and positive scale, the Gamma kernel-pole
residue norm equals the completed logarithmic derivative norm at zero divided
by sqrt(x). Gamma recurrence gives regularized pole coefficient one.
This exact identity removes the kernel-dependent constant from endpoint bounds. -/
theorem gamma_poleResidue_norm {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hne : χ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    ‖MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
          (-1 / 2)‖ =
      ‖logDeriv χ.completedLFunction 0‖ / Real.sqrt x := by
  have he : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  simp only [MellinKernel.weightedResidue, ite_true]
  rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_shifted_completed hne, he, norm_mul,
    norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hr : gammaMellinKernel.regularized (-1 / 2) = 1 := by
    change Complex.Gamma (-1 / 2 + 1 / 2 + 1) = 1
    rw [show (-1 / 2 : ℂ) + 1 / 2 + 1 = 1 by ring, Complex.Gamma_one]
  rw [hr, norm_one, one_mul]
  norm_num only [Complex.div_ofNat_re, Complex.neg_re, Complex.one_re]
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]

/-- Under GRH, primitive nonprincipal conductor m≥3 at most ambient q≥20000
has Gamma pole residue norm at most ((7/6)log(q)+4)/sqrt(x), for x>0.
Apply the ambient xi endpoint bound to the exact Gamma residue identity.
Small primitive conductors are retained in the fixed-kernel comparison. -/
theorem gamma_poleResidue_le_ambient {q m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    ‖MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
          (-1 / 2)‖ ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := by
  rw [gamma_poleResidue_norm hne hx]
  exact
    div_le_div_of_nonneg_right
      (norm_completedLogDeriv_zero_le_ambient_affine_log hq hm hmq hp hne hGRH) (Real.sqrt_nonneg x)

/-- Under GRH and primitive nonprincipal data of modulus q≥8, the Gamma pole
residue is bounded by ((7/6)log(q)+4)/sqrt(x) at every positive scale.
Combine the completed endpoint estimate with the exact pole coefficient one.
This supplies an explicit residue error without an eventual scale restriction. -/
theorem gamma_poleResidue_le_affine_log {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 8 ≤ q)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    ‖MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
          (-1 / 2)‖ ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := by
  rw [gamma_poleResidue_norm hne hx]
  exact
    div_le_div_of_nonneg_right (norm_completedLogDeriv_zero_le_affine_log hq hp hne hGRH)
      (Real.sqrt_nonneg x)

end PseudoPrime.LLS.PaperStatements
