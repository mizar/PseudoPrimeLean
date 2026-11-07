/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSharpDeficit
public import PseudoPrime.LLS.PaperStatements.GaussianMomentCapsCertified

/-! # Certified Gaussian principal deficit -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and the stated positive scale and narrow width, the actual
Gaussian principal deficit has an explicit lower bound at cutoff ratio 21/10.
The Gaussian moments and main cutoff mass are kernel-certified; no moment
hypotheses remain. This is the numerical input for the pair-character witness gap. -/
theorem gaussian_deficit_certified (hRH : RiemannHypothesis) {x h : ℝ} (hx : 0 < x)
    (hlx : 1 ≤ (21 / 10 : ℝ) * x) (hh : 0 < h) (hh1 : h ≤ 1 / 32) :
    4 *
          (Real.sqrt x * (81470555 / 100000000 : ℝ) -
            (7 / 50 : ℝ) / Real.sqrt x *
              ((32 / 63 : ℝ) * h * ((21 / 10 : ℝ) * x) +
                (231 / 2500 : ℝ) * (Real.sqrt ((21 / 10 : ℝ) * x) + 1) / h +
                1839 / 1000) -
            ((231 / 5000 : ℝ) * Real.sqrt ((21 / 10 : ℝ) * x) +
                (1839 / 1000 : ℝ) * Real.log ((21 / 10 : ℝ) * x) +
                2) /
              Real.sqrt x) -
        (Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13) ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊(21 / 10 : ℝ) * x⌋₊,
            (LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
                n).re) -
        (∑' n : ℕ,
            LLS.PaperStatements.gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x
              n).re := by
  have hc := LLS.PaperStatements.gaussian_moment_caps_21_10
  have h :=
    gaussian_deficit_of_moment_caps hRH hx (l := 21 / 10) (by norm_num only) hlx hh hh1 hc.1 hc.2
  have hm := Analysis.gaussianGammaCutoff_mass_gt_target
  rw [Analysis.integral_gaussianGammaProfile_div_sqrt (by norm_num only)] at hm
  have hm' := mul_le_mul_of_nonneg_left hm.le (Real.sqrt_nonneg x)
  linarith only [h, hm']

end PseudoPrime.PrimeTestBounds.MillerRabin
