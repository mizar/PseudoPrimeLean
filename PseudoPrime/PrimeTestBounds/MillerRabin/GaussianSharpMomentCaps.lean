/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.SharpGaussianPrincipalBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticNarrowRelativePsi

/-! # Sharp Gaussian lower bound with moment caps -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, narrow relative width and two explicit Gaussian moment caps imply
the sharp finite principal lower bound. The Chebyshev deficit is first bounded
before applying the nonnegative profile moment; the remaining moment costs at
most one. This is the scalar form needed for the high-range comparison. -/
theorem gaussian_lower_of_moment_caps (hRH : RiemannHypothesis) {x l h : ℝ} (hx : 0 < x)
    (hl : 0 ≤ l) (hlx : 1 ≤ l * x) (hh : 0 < h) (hh1 : h ≤ 1 / 32)
    (hF : (∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand l v) ≤ 7 / 50)
    (hC :
      l * (∫ v : ℝ, LLS.PaperStatements.gaussianEndpointDensity l v) +
          2 * Real.exp (-1) * Real.exp (1 / 16 : ℝ) ≤
        1) :
    Real.sqrt x * (∫ v : ℝ, Analysis.gaussianGammaCutoffIntegrand l v) -
        (7 / 50 : ℝ) / Real.sqrt x *
          ((32 / 63 : ℝ) * h * (l * x) + (231 / 2500 : ℝ) * (Real.sqrt (l * x) + 1) / h +
            1839 / 1000) -
        ((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) /
          Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
        (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
            n).re := by
  let D : ℝ :=
    (32 / 63 : ℝ) * h * (l * x) + (231 / 2500 : ℝ) * (Real.sqrt (l * x) + 1) / h + 1839 / 1000
  let E : ℝ := (231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2
  let F : ℝ := ∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand l v
  let C : ℝ :=
    l * (∫ v : ℝ, LLS.PaperStatements.gaussianEndpointDensity l v) +
      2 * Real.exp (-1) * Real.exp (1 / 16 : ℝ)
  have hF0 : 0 ≤ F :=
    MeasureTheory.integral_nonneg (fun v ↦ (Analysis.gaussianGammaProfileIntegrand_pos l v).le)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    have hm :=
      mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 32 / 63) hh.le) (mul_nonneg hl hx.le)
    have hn :=
      div_nonneg
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 2500)
          (add_nonneg (Real.sqrt_nonneg (l * x)) zero_le_one))
        hh.le
    linarith only [hm, hn]
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    nlinarith only [Real.sqrt_nonneg (l * x), Real.log_nonneg hlx]
  have hdef : l * x - Chebyshev.psi (l * x) ≤ D := by
    have hp := psi_relative_lower_32 hRH hh hh1 (mul_nonneg hl hx.le)
    dsimp only [D]
    linarith only [hp]
  have hp := mul_le_mul hdef hF hF0 hD0
  have hq := mul_le_mul_of_nonneg_left hC hE0
  have hs := Real.sqrt_pos.mpr hx
  have hp' := div_le_div_of_nonneg_right hp hs.le
  have hq' := div_le_div_of_nonneg_right hq hs.le
  have hm := LLS.PaperStatements.gaussian_level_one_lower_sharp hRH hx hl hlx
  change
    Real.sqrt x * _ - ((l * x - Chebyshev.psi (l * x)) / Real.sqrt x) * F - (E / Real.sqrt x) * C ≤
      _ at hm
  change _ - ((7 / 50 : ℝ) / Real.sqrt x) * D - E / Real.sqrt x ≤ _
  have hp'' :
    ((l * x - Chebyshev.psi (l * x)) / Real.sqrt x) * F ≤ ((7 / 50 : ℝ) / Real.sqrt x) * D := by
    convert hp' using 1 <;> ring
  have hq'' : (E / Real.sqrt x) * C ≤ E / Real.sqrt x := by convert hq' using 1 <;> ring
  linarith only [hm, hp'', hq'']

end PseudoPrime.PrimeTestBounds.MillerRabin
