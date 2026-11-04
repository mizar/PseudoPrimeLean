/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveMonotone

/-! # Cumulative envelope for the adaptive triangular witness bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The adaptive cumulative cap retains the earlier four-ninths bound at the entrance
and the previous floor value at the later coefficient switch. The remaining term
is the square of the adaptive radius at logarithmic scale `L`. -/
noncomputable def triangularAdaptiveCap (L : ℝ) : ℝ :=
  max ((4 / 9 : ℝ) * (30000000000 : ℝ) ^ 2)
    ((max (triangularAdaptiveRadius L * L) (triangularFloorHistory L)) ^ 2)

/-- Under GRH, the least prime witness for an odd composite with logarithm at most `L`
is bounded by the adaptive cap. Scaled-radius monotonicity retains the floor-switch
history, while the four-ninths bound handles inputs before the adaptive entrance. -/
theorem leastPrime_le_triangularScale (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) (L : ℝ) (hlog : Real.log n ≤ L) :
    (compositeLeastPrime n : ℝ) ≤ triangularAdaptiveCap L := by
  by_cases hhigh : (30000000000 : ℝ) ≤ Real.log n
  · obtain ⟨p, hp, hb, hr⟩ := triangularAdaptive_prime_witness hn ho hc hGRH hhigh
    have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
    have ha : 0 ≤ triangularAdaptiveRadius (Real.log n) := by
      have hh := (triangularAdaptiveRadius_bounds hhigh).1
      linarith only [hh]
    have hscaled := triangular_scaled_radius_le hhigh hlog
    have hs := pow_le_pow_left₀ (mul_nonneg ha (by linarith only [hhigh])) hscaled 2
    rw [mul_pow] at hs
    exact ((Nat.cast_le.mpr hm).trans hb).trans (hs.trans (le_max_right _ _))
  · have hprev := leastPrime_le_fourNinthsScale hGRH hn ho hc 30000000000 (le_of_not_ge hhigh)
    exact hprev.trans ((min_le_right _ _).trans (le_max_left _ _))

/-- The cumulative envelope takes the minimum of the previous mean bound and the
adaptive cap at `log N`. This keeps all earlier candidates and both entry histories. -/
noncomputable def triangularAdaptiveCumulative (N : ℕ) : ℝ :=
  min (meanCumulative N) (triangularAdaptiveCap (Real.log N))

/-- Under GRH, the maximum least prime witness up to `N` is bounded by the adaptive
cumulative envelope. The proof combines the preceding cumulative bound with the
uniform scale bound, retaining both candidates in the final minimum. -/
theorem cumulativeLeastPrime_le_triangular
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (N : ℕ) :
    (cumulativeLeastPrime N : ℝ) ≤ triangularAdaptiveCumulative N := by
  have hcap : ∀ L, 0 ≤ triangularAdaptiveCap L := by
    intro L
    exact (by norm_num only : (0 : ℝ) ≤ (4 / 9) * (30000000000 : ℝ) ^ 2).trans (le_max_left _ _)
  have h :=
    cumulativeLeastPrime_le_base triangularAdaptiveCap hcap
      (fun hn ho hc L hlog ↦ leastPrime_le_triangularScale hGRH hn ho hc L hlog) [] hGRH N
  have h' : (cumulativeLeastPrime N : ℝ) ≤ triangularAdaptiveCap (Real.log N) := by
    simpa only [baseHistory] using h
  exact le_min (cumulativeLeastPrime_le_mean hGRH N) h'

end PseudoPrime.PrimeTestBounds.MillerRabin
