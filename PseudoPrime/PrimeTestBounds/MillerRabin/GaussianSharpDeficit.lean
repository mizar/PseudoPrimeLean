/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSharpMomentCaps
public import PseudoPrime.LLS.PaperStatements.GaussianPrincipalConstantBounds

/-! # Gaussian principal deficit from sharp moment caps -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and the two stated Gaussian moment caps, the sharp finite lower
bound and the full principal upper bound give a lower bound for the principal
deficit. This is the numerical side of the actual pair-character witness gap. -/
theorem gaussian_deficit_of_moment_caps (hRH : RiemannHypothesis) {x l h : ℝ} (hx : 0 < x)
    (hl : 0 ≤ l) (hlx : 1 ≤ l * x) (hh : 0 < h) (hh1 : h ≤ 1 / 32)
    (hF : (∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand l v) ≤ 7 / 50)
    (hC :
      l * (∫ v : ℝ, LLS.PaperStatements.gaussianEndpointDensity l v) +
          2 * Real.exp (-1) * Real.exp (1 / 16 : ℝ) ≤
        1) :
    4 *
          (Real.sqrt x * (∫ v : ℝ, Analysis.gaussianGammaCutoffIntegrand l v) -
            (7 / 50 : ℝ) / Real.sqrt x *
              ((32 / 63 : ℝ) * h * (l * x) + (231 / 2500 : ℝ) * (Real.sqrt (l * x) + 1) / h +
                1839 / 1000) -
            ((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) /
              Real.sqrt x) -
        (Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13) ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
            (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                n).re) -
        (∑' n : ℕ,
            LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              n).re := by
  have hlo := gaussian_lower_of_moment_caps hRH hx hl hlx hh hh1 hF hC
  have hup := LLS.PaperStatements.gaussian_level_one_sum_upper_constant hRH hx
  linarith only [hlo, hup]

end PseudoPrime.PrimeTestBounds.MillerRabin
