/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteData
public import PseudoPrime.LLS.PaperStatements.EndpointFinitePrincipal
public import PseudoPrime.LLS.EndpointLowPrime

/-! # Positive endpoint gap certificates for thirteen finite principal profiles -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A positive gained-gap anchor extends to the actual logarithm and smaller levels. -/
theorem finitePrincipal_gap_from_quad {L L₀ y z₀ a b dR dS : ℝ} (hL : L ≤ L₀) (hy : 1 ≤ y)
    (hz0 : 0 ≤ z₀) (hz : z₀ ≤ Real.log y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoly :
      ∀ z : ℝ,
        finitePrincipalGap L₀ (2096 / 1831) y z dR dS -
            finitePrincipalGap L₀ (2096 / 1831) y z₀ dR dS =
          a * (z ^ 2 - z₀ ^ 2) + b * (z - z₀))
    (hanchor : 0 < finitePrincipalGap L₀ (2096 / 1831) y z₀ dR dS) :
    0 < finitePrincipalGap L (2096 / 1831) y (Real.log y) dR dS := by
  have hzpos := hz0.trans hz
  have hsq := (sq_le_sq₀ hz0 hzpos).mpr hz
  have h1 := mul_nonneg ha (sub_nonneg.mpr hsq)
  have h2 := mul_nonneg hb (sub_nonneg.mpr hz)
  have hident := hpoly (Real.log y)
  have hgap : 0 < finitePrincipalGap L₀ (2096 / 1831) y (Real.log y) dR dS := by
    linarith only [hanchor, hident, h1, h2]
  exact hgap.trans_le (finitePrincipalGap_antitone hy hzpos hL)

/-- Both gained-gap quadratic coefficients are nonnegative at every finite profile cap. -/
theorem finitePrincipal_coefficients (f : Analysis.FinitePrimeProfile) :
    0 ≤ lowPrimeA f.radius ∧
      0 ≤ lowPrimeB f.logCap f.radius + 2 * (f.radius : ℝ) ^ 2 * f.deltaR := by
  cases f <;>
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, Analysis.FinitePrimeProfile.radius,
      Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.deltaR,
      Analysis.FinitePrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat, ↓reduceIte, and_self]

/-- Every strengthened finite-principal cap has a strictly positive rational gap anchor. -/
theorem finitePrincipal_anchor (f : Analysis.FinitePrimeProfile) :
    0 < finitePrincipalGap f.logCap (2096 / 1831) f.radius f.logLo f.deltaR f.deltaS := by
  cases f <;>
    norm_num only [finitePrincipalGap, endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, Analysis.FinitePrimeProfile.radius,
      Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.logLo,
      Analysis.FinitePrimeProfile.deltaR, Analysis.FinitePrimeProfile.deltaS,
      Analysis.FinitePrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat, ↓reduceIte]

/-- Every finite profile has positive gained gap through its stated logarithmic cap. -/
theorem finitePrincipal_profile_gap (f : Analysis.FinitePrimeProfile) {L : ℝ} (hL : L ≤ f.logCap) :
    0 < finitePrincipalGap L (2096 / 1831) f.radius (Real.log f.radius) f.deltaR f.deltaS := by
  have hr := Analysis.finitePrincipal_radius_bounds f
  have hy : (1 : ℝ) ≤ f.radius := by linarith only [hr.1]
  have hn : (f.radius : ℝ) ≠ 0 := ne_of_gt (by linarith only [hr.1])
  have hz : (0 : ℝ) ≤ f.logLo := by
    cases f <;> norm_num only [Analysis.FinitePrimeProfile.logLo, Rat.cast_div, Rat.cast_ofNat]
  apply
    finitePrincipal_gap_from_quad (a := lowPrimeA f.radius) (b :=
      lowPrimeB f.logCap f.radius + 2 * (f.radius : ℝ) ^ 2 * f.deltaR) hL hy hz
      (Analysis.finitePrincipal_log_bounds f).1 (finitePrincipal_coefficients f).1
      (finitePrincipal_coefficients f).2
  · intro z
    dsimp only [finitePrincipalGap]
    rw [lowPrime_gap_quad hn, lowPrime_gap_quad hn]
    ring
  · exact finitePrincipal_anchor f

end PseudoPrime.LLS.PaperStatements
