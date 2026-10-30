/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSurplusPrefix
public import PseudoPrime.LLS.GammaSeedLogMoment

/-! # Stronger actual Gaussian prefixes from a finite surplus -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Any actual Gamma prefix lower bound gains the independently certified finite surplus.
The difference sum and the Gamma sum use exactly the same finite cutoff.
Only their separately certified contributions are added. -/
theorem gaussian_prefix_add_surplus {b P : ℝ} (hb : 100 ≤ b)
    (hP : P ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n) :
    (17 / 20 : ℝ) * P + 73 / 100 ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hs := gaussianSurplus_prefix hb
  simp only [gaussianSurplus_mangoldt_eq, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hP (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  linarith only [hs, hm]

/-- Under RH, the actual Gaussian prefix beyond 35000 is at least 5.54117.
Add only the certified surplus 0.73 to seventeen twentieths of the actual Gamma bound. -/
theorem gaussian_prefix35000_surplus (hRH : RiemannHypothesis) {b : ℝ} (hb : 35000 ≤ b) :
    (554117 / 100000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have h := gaussian_prefix_add_surplus (by linarith only [hb]) (gamma_prefix35000_moment hRH hb)
  norm_num only at h
  exact h

/-- Under RH, the actual Gaussian prefix beyond 50000 is at least 5.645295.
Retain the original finite cutoff while adding the same independently checked surplus. -/
theorem gaussian_prefix50000_surplus (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b) :
    (1129059 / 200000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have h := gaussian_prefix_add_surplus (by linarith only [hb]) (gamma_prefix50000_moment hRH hb)
  norm_num only at h
  exact h

end PseudoPrime.LLS
