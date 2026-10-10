/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMellin
public import PseudoPrime.LLS.PaperDefinitions

/-! # Transform, endpoint and mass identities for the gamma kernel

Mellin inversion proves the density of the Section 6.3 kernel on every allowed
line. Reflection reduces its mass to a real hyperbolic-cosine integral.
These identities do not assert the remaining sharp mass bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On every line `c>-1/2`, the inverse Mellin transform of shifted gamma
is the real density `sqrt(u) exp(-u)` for positive `u`. Convert the paper's
integral convention to Mathlib's and use pointwise Mellin inversion.
This proves the gamma kernel's transform identity and line independence. -/
theorem inverseMellin_gamma {c u : ℝ} (hc : -1 / 2 < c) (hu : 0 < u) :
    inverseMellin (fun s : ℂ ↦ Complex.Gamma (s + 1 / 2)) c u =
      (Real.sqrt u * Real.exp (-u) : ℝ) := by
  rw [← Analysis.mellinInv_gamma_half_of_pos (by linarith only [hc] : 0 < c + 1 / 2) hu]
  unfold inverseMellin mellinInv
  rw [Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [smul_eq_mul, mul_comm]

/-- For every `c>-1/2` and positive argument, the gamma inverse-Mellin
integrand is absolutely integrable. Gamma is integrable on the shifted line,
and the positive-base Mellin power has constant norm along the line.
This supplies the integrability field of the Section 6.3 kernel. -/
theorem integrable_inverseMellin_gamma {c u : ℝ} (hc : -1 / 2 < c) (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Complex.Gamma (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) := by
  have hcp : 0 < c + 1 / 2 := by linarith only [hc]
  have hi :
    MeasureTheory.Integrable (fun t : ℝ ↦ Complex.Gamma (((c : ℂ) + Complex.I * t) + 1 / 2)) := by
    apply (Analysis.integrable_Gamma_vertical hcp).congr
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    congr 1
    rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hp : Continuous (fun t : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
  apply hi.mul_bdd (c := u ^ (-c)) hp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  exact le_rfl

/-- An admissible kernel whose function is shifted gamma has real transform
`sqrt(u) exp(-u)` at positive arguments. Use the proved inverse-Mellin identity.
This removes the transform-identification input from the gamma specialization. -/
theorem gamma_transform_of_function (K : MellinKernel)
    (hK : K.function = fun s : ℂ ↦ Complex.Gamma (s + 1 / 2)) {u : ℝ} (hu : 0 < u) :
    (K.transform u).re = Real.sqrt u * Real.exp (-u) := by
  rw [MellinKernel.transform, hK, inverseMellin_gamma (by norm_num only) hu]
  exact Complex.ofReal_re _

/-- A shifted-gamma kernel has real value one at `s=1/2`, by `Gamma(1)=1`.
This removes the endpoint-identification input from the gamma specialization. -/
theorem gamma_endpoint_of_function (K : MellinKernel)
    (hK : K.function = fun s : ℂ ↦ Complex.Gamma (s + 1 / 2)) : (K.function (1 / 2)).re = 1 := by
  rw [hK]
  dsimp only
  have he : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num only
  rw [he, Complex.Gamma_one, Complex.one_re]

/-- The mass of a shifted-gamma kernel is the integral of
`sqrt(pi/cosh(pi*t))`, divided by `2*pi`. Euler reflection identifies each norm.
This reduces the remaining mass certificate to a real numerical integral. -/
theorem gamma_mass_of_function (K : MellinKernel)
    (hK : K.function = fun s : ℂ ↦ Complex.Gamma (s + 1 / 2)) :
    K.mass = (∫ t : ℝ, Real.sqrt (Real.pi / Real.cosh (Real.pi * t))) / (2 * Real.pi) := by
  unfold MellinKernel.mass
  rw [hK]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [add_comm]
  exact Analysis.norm_Gamma_half_add_I t

end PseudoPrime.LLS.PaperStatements
