/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianPrefixSurplus

/-! # The actual thousand-term Gaussian prefix with its finite surplus

This leaf combines the existing Gamma moment prefix and the separately certified Gaussian
surplus at the same cutoff. It changes no finite certificate and keeps this new thousand-term
consumer separate from the established 35000 and 50000 prefix consumers.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH, every actual Gaussian prefix beyond 1000 has the displayed stronger credit.
Input: RH and a real cutoff at least 1000. Claim: the prefix is at least 4.342585.
Proof: add the existing finite surplus to the Gamma moment prefix, with no new enumeration.
Role: supply the actual prefix to the improved thousand-term MR profile. -/
theorem gaussian_prefix1000_surplus (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (868517 / 200000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have h :=
    gaussian_prefix_add_surplus (le_trans (by norm_num only : (100 : ℝ) ≤ 1000) hb)
      (gamma_prefix1000_moment hRH hb)
  norm_num only at h
  exact h

end PseudoPrime.LLS
