/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedFixedEnvelope

/-! # Cumulative caps for the three fixed profile candidates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The profile cap combines its coefficient with the triangular entrance history. -/
noncomputable def fixedProfileCap (f : TriangularProfile) (L : ℝ) : ℝ :=
  max (triangularAdaptiveCap f.T) (f.C * L ^ 2)

/-- Under GRH, the profile cap bounds the least witness at every input below the common scale. -/
theorem leastPrime_le_fixedScale (f : TriangularProfile)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ fixedProfileCap f L := by
  by_cases hhigh : f.T ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := exists_prime_triangularProfile f hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have hlog0 : 0 ≤ Real.log n := by linarith only [f.entry, hhigh]
    have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
    have hs := pow_le_pow_left₀ hlog0 hlog 2
    have hh := mul_le_mul_of_nonneg_left hs hC
    exact ((Nat.cast_le.mpr hm).trans hb).trans (hh.trans (le_max_right _ _))
  · have hprev := leastPrime_le_triangularScale hGRH hn ho hc f.T (le_of_not_ge hhigh)
    exact hprev.trans (le_max_left _ _)

/-- The cumulative envelope takes the minimum of the Gaussian bound and three fixed-profile caps. -/
noncomputable def fixedImprovedCumulative (N : ℕ) : ℝ :=
  min (gaussianAdaptiveCumulative N)
    (min (fixedProfileCap improvedProfile03869 (Real.log N))
      (min (fixedProfileCap improvedProfile03552 (Real.log N))
        (fixedProfileCap improvedProfile03134 (Real.log N))))

/-- Under GRH, the fixed-profile cumulative envelope bounds the maximum least witness. -/
theorem cumulativeLeastPrime_le_fixedImproved
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ fixedImprovedCumulative N := by
  have hbound (f : TriangularProfile) :
    (cumulativeLeastPrime N : ℝ) ≤ fixedProfileCap f (Real.log N) := by
    have hcap : ∀ L, 0 ≤ fixedProfileCap f L := by
      intro L
      have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
      exact (mul_nonneg hC (sq_nonneg L)).trans (le_max_right _ _)
    have h :=
      cumulativeLeastPrime_le_base (fixedProfileCap f) hcap
        (fun hn ho hc L hlog ↦ leastPrime_le_fixedScale f hGRH hn ho hc L hlog) [] hGRH N
    simpa only [baseHistory] using h
  exact
    le_min (cumulativeLeastPrime_le_gaussianAdaptive hGRH N)
      (le_min (hbound improvedProfile03869)
        (le_min (hbound improvedProfile03552) (hbound improvedProfile03134)))

end PseudoPrime.PrimeTestBounds.MillerRabin
