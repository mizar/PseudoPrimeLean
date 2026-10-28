/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianPrefixComparison
public import PseudoPrime.LLS.GammaCheckpoint1000Sharp

/-! # The retained Gaussian prefix at cutoff 1000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and b>=1000, the Gaussian prefix is at least 7191/2000.
Recompose the existing Gamma lower bound and the pointwise factor 17/20.
This retains the unrounded prefix mass without new nodes or finite input data. -/
theorem gaussian_prefix1000_sharp {b : ℝ} (hRH : RiemannHypothesis) (hb : 1000 ≤ b) :
    (7191 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hg := gamma_prefix1000_sharp hRH hb
  have hs :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  rw [← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  linarith only [hm, hs]

end PseudoPrime.LLS
