/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.LLS.GammaCheckpoint35000

/-! # Signed Gaussian prefix comparison with arbitrary certified cutoff mass -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, every Gaussian prefix with cutoff at least 35000 has mass at least 47/10.
Scale the certified Gamma prefix by 17/20 and sum the pointwise weight inequality.
This supplies the shorter prefix used by the log240 MR budget. -/
theorem gaussian_prefix35000_lower {b : ℝ} (hRH : RiemannHypothesis) (hb : 35000 ≤ b) :
    (47 / 10 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hg := gamma_prefix35000_lower hRH hb
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  rw [← Finset.mul_sum] at hs
  have h := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  linarith only [h, hs]

end PseudoPrime.LLS
