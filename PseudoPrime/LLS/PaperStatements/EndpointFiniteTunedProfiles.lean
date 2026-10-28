/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteCredits
public import PseudoPrime.LLS.PaperStatements.EndpointFiniteProfiles

/-! # Positive endpoint gaps from profile-specific finite principal credits -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Both gained-gap quadratic coefficients are nonnegative at every finite profile cap. -/
theorem finiteTuned_coefficients (f : Analysis.FinitePrimeProfile) :
    0 ≤ lowPrimeA f.radius ∧
      0 ≤ lowPrimeB f.tunedCap f.radius + 2 * (f.radius : ℝ) ^ 2 * f.tunedR := by
  cases f <;>
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, Analysis.FinitePrimeProfile.radius,
      Analysis.FinitePrimeProfile.tunedCap, Analysis.FinitePrimeProfile.tunedR,
      Analysis.FinitePrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat, ↓reduceIte, and_self]

/-- Every strengthened finite-principal cap has a strictly positive rational gap anchor. -/
theorem finiteTuned_anchor (f : Analysis.FinitePrimeProfile) :
    0 < finitePrincipalGap f.tunedCap (2096 / 1831) f.radius f.logLo f.tunedR f.tunedS := by
  cases f <;>
    norm_num only [finitePrincipalGap, endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, Analysis.FinitePrimeProfile.radius,
      Analysis.FinitePrimeProfile.tunedCap, Analysis.FinitePrimeProfile.logLo,
      Analysis.FinitePrimeProfile.tunedR, Analysis.FinitePrimeProfile.tunedS,
      Analysis.FinitePrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat, ↓reduceIte]

/-- Every finite profile has positive gained gap through its stated logarithmic cap. -/
theorem finiteTuned_profile_gap (f : Analysis.FinitePrimeProfile) {L : ℝ} (hL : L ≤ f.tunedCap) :
    0 < finitePrincipalGap L (2096 / 1831) f.radius (Real.log f.radius) f.tunedR f.tunedS := by
  have hr := Analysis.finitePrincipal_radius_bounds f
  have hy : (1 : ℝ) ≤ f.radius := by linarith only [hr.1]
  have hn : (f.radius : ℝ) ≠ 0 := ne_of_gt (by linarith only [hr.1])
  have hz : (0 : ℝ) ≤ f.logLo := by
    cases f <;> norm_num only [Analysis.FinitePrimeProfile.logLo, Rat.cast_div, Rat.cast_ofNat]
  apply
    finitePrincipal_gap_from_quad (a := lowPrimeA f.radius) (b :=
      lowPrimeB f.tunedCap f.radius + 2 * (f.radius : ℝ) ^ 2 * f.tunedR) hL hy hz
      (Analysis.finitePrincipal_log_bounds f).1 (finiteTuned_coefficients f).1
      (finiteTuned_coefficients f).2
  · intro z
    dsimp only [finitePrincipalGap]
    rw [lowPrime_gap_quad hn, lowPrime_gap_quad hn]
    ring
  · exact finiteTuned_anchor f

end PseudoPrime.LLS.PaperStatements
