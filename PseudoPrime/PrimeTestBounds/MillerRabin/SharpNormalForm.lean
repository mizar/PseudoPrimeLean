/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpIntervalSelection
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFinitePointwise
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianNormalAbsorption
public import PseudoPrime.Analysis.GaussianSeededSharpMonotone

/-! # The regular-range normal form of the sharp selected envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If two new candidates dominate their old counterparts, their intersection
absorbs the old counterparts from a common pointwise minimum. Compare both inequalities directly. -/
theorem min_absorb_gaussianSeeded (P G S R T : ℝ) (hG : G ≤ R) (hS : S ≤ T) :
    min (min P (min R T)) (min G S) = min P (min G S) := by
  apply le_antisymm
  · exact le_min ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _)
  · apply le_min
    · exact
        le_min (min_le_left _ _)
          (le_min ((min_le_right _ _).trans ((min_le_left _ _).trans hG))
            ((min_le_right _ _).trans ((min_le_right _ _).trans hS)))
    · exact min_le_right _ _

/-- Above the final finite cap, the finite selected function equals the current refined selection.
Rewrite both numerical guarded-selection identities around the existing fallback theorem. -/
theorem lowFiniteSelected_eq_refined {n : ℕ} (hn : 1 < n) (hL : 12373 / 1000 < Real.log n) :
    lowFiniteSelected n = refinedSelectedEnvelope n := by
  rw [← lowFinite_eq_selected hn, lowFinite_eq_refined_of_log hn hL, refined_eq_selected hn]

/-- Above the last finite cap and below scale 63, the current refined selection
is exactly the pointwise cutoff. All analytic guards and finite constants are inactive. -/
theorem refined_eq_pointwise_low {n : ℕ} (hn : 1 < n) (hL : 12373 / 1000 < Real.log n)
    (hU : Real.log n < 63) :
    refinedSelectedEnvelope n = LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
  rw [refinedSelected_eq_low hU, ← lowPrimeTight_eq_selected hn,
    lowPrimeTight_eq_next_of_log (by linarith only [hL]),
    next_eq_pointwise hn (by linarith only [hL]) (by linarith only [hU])]

/-- On scales [63,100), the current refined selection consists of the pointwise
cutoff and its two Gaussian candidates. Gamma remains inactive before its entrance. -/
theorem refined_eq_pointwise_mix {n : ℕ} (hn : 1 < n) (hL : 63 ≤ Real.log n)
    (hU : Real.log n < 100) :
    refinedSelectedEnvelope n =
      min (LLS.PaperStatements.pointwiseCutoff (Real.log n))
        (min (Analysis.gaussianRecoveredBound (Real.log n))
          (Analysis.gaussianRecoveredSeeded (Real.log n))) := by
  rw [refinedSelected_eq_before101 hL (by linarith only [hU]), ← lowPrimeTight_eq_selected hn,
    lowPrimeTight_eq_next_of_log (by linarith only [hL]),
    next_eq_pointwise hn (by linarith only [hL]) hU]

/-- The fine Gaussian family is at least 8000 on the whole real scale.
Weaken its exact rational fourth-power floor for the low-domain guard comparison. -/
theorem gaussianLowFamily_floor8000 (L : ℝ) : (8000 : ℝ) ≤ Analysis.gaussianLowFamily L := by
  have h := gaussianLowFamily_floor L
  norm_num only at h
  linarith only [h]

/-- For inputs at least 3000 with scale below 100, the sharp selection equals
the minimum of the monotone finite-pointwise function and the two analytic families.
Use the thirteen exact low intervals, then remove the scale-63 guard by certified floors. -/
theorem sharpSelected_eq_regular_low {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 100) :
    sharpSelectedEnvelope n =
      min (lowFinitePointwise (Real.log n))
        (min (Analysis.gaussianLowFamily (Real.log n))
          (Analysis.gaussianSeededSharp (Real.log n))) := by
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have h8 : (8 : ℝ) < Real.log n := Analysis.eight_lt_log_level hN
  have hG := gaussianLowFamily_floor8000 (Real.log n)
  have hS := Analysis.gaussianSeededSharp_floor (Real.log n)
  by_cases hcap : Real.log n ≤ 12373 / 1000
  · have h63 : Real.log n < (63 : ℝ) := by linarith only [hcap]
    have h73 := lowFiniteSelected_le73 hn hN hcap
    rw [sharpSelected_eq_low hN h63, lowFinitePointwise_eq_selected hn hN hcap,
      min_eq_left (le_min (by linarith only [h73, hG]) (by linarith only [h73, hS]))]
  · have hlast : (12373 / 1000 : ℝ) < Real.log n := lt_of_not_ge hcap
    rw [lowFinitePointwise_eq_pointwise hlast]
    by_cases h63 : Real.log n < 63
    · have hP := LLS.PaperStatements.pointwiseCutoff_lt_square h8
      have hsq : Real.log n ^ 2 < (3969 : ℝ) := by nlinarith only [h8, h63]
      rw [sharpSelected_eq_low hN h63, lowFiniteSelected_eq_refined hn hlast,
        refined_eq_pointwise_low hn hlast h63,
        min_eq_left (le_min (by linarith only [hP, hsq, hG]) (by linarith only [hP, hsq, hS]))]
    · have he : (63 : ℝ) ≤ Real.log n := le_of_not_gt h63
      rw [sharpSelected_eq_analytic hN he (by linarith only [hU]),
        lowFiniteSelected_eq_refined hn hlast, refined_eq_pointwise_mix hn he hU]
      exact
        min_absorb_gaussianSeeded _ _ _ _ _
          (gaussianLowFamily_lt_recovered (by linarith only [he])).le
          (Analysis.gaussianSeededSharp_le_seeded he)

/-- For inputs at least 3000 below scale thirty billion, the sharp selection equals
the minimum of the monotone finite-pointwise function and both analytic families.
Join the low-domain formula with the independent high-domain absorption theorem. -/
theorem sharpSelected_eq_regular {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 30000000000) :
    sharpSelectedEnvelope n =
      min (lowFinitePointwise (Real.log n))
        (min (Analysis.gaussianLowFamily (Real.log n))
          (Analysis.gaussianSeededSharp (Real.log n))) := by
  by_cases h100 : Real.log n < 100
  · exact sharpSelected_eq_regular_low hN h100
  · have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
    have he : (100 : ℝ) ≤ Real.log n := le_of_not_gt h100
    have hlast : (12373 / 1000 : ℝ) < Real.log n := by linarith only [he]
    rw [sharpSelected_eq_analytic hN (by linarith only [he]) hU,
      lowFiniteSelected_eq_refined hn hlast, lowFinitePointwise_eq_pointwise hlast,
      min_refined_gaussianSeeded_eq hn he hU]
    apply Eq.symm
    apply min_eq_right
    exact (min_le_left _ _).trans (gaussianLowFamily_lt_pointwise he).le

end PseudoPrime.PrimeTestBounds.MillerRabin
