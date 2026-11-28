/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186AbelBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CompCert

/-! # K186 rejecting prime on the far Gaussian range -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd uniform Korselt triple with logarithm at least
thirty trillion has a rejecting prime within the Gaussian cutoff. The
compensation integrals use the certified signed dyadic partition. -/
theorem uniform_gaussian_far {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 30000000000000 ≤ Real.log n) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  obtain ⟨hi, hv⟩ := k186_comp_cert_caps
  exact
    uniform_k186_far_of_comp_caps hn ho hu hGRH hL
      (k186_scaled_comp_of_cap (hi.trans (by norm_num only))) (hv.trans (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin
