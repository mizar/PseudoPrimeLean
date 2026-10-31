/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointPrime79PlusData
public import PseudoPrime.LLS.PaperStatements.EndpointFiniteProfiles
public import PseudoPrime.LLS.PaperStatements.EndpointPointwiseGrowth

/-! # Positive fixed-79 gap after adding the atoms 79 and 81 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The fixed-79 gained gap has nonnegative quadratic coefficients at its cap. -/
theorem prime79Plus_coefficients :
    0 ≤ lowPrimeA prime79PlusRadius ∧
      0 ≤
        lowPrimeB prime79PlusCap prime79PlusRadius +
          2 * (prime79PlusRadius : ℝ) ^ 2 * prime79PlusCreditR := by
  norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, prime79PlusRadius, prime79PlusCap,
    prime79PlusCreditR, Rat.cast_div, Rat.cast_ofNat, and_self]

/-- The fixed-79 gained gap is strictly positive at the lower logarithm anchor. -/
theorem prime79Plus_anchor :
    0 <
      finitePrincipalGap prime79PlusCap (2096 / 1831) prime79PlusRadius prime79PlusLogLo
        prime79PlusCreditR prime79PlusCreditS := by
  norm_num only [finitePrincipalGap, endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
    Analysis.pointwiseReciprocalLoss, prime79PlusCap, prime79PlusRadius, prime79PlusLogLo,
    prime79PlusCreditR, prime79PlusCreditS, Rat.cast_div, Rat.cast_ofNat]

/-- The fixed-79 gained gap is positive at the actual logarithm through its tuned cap. -/
theorem prime79Plus_gap {L : ℝ} (hL : L ≤ prime79PlusCap) :
    0 <
      finitePrincipalGap L (2096 / 1831) prime79PlusRadius (Real.log prime79PlusRadius)
        prime79PlusCreditR prime79PlusCreditS := by
  apply
    finitePrincipal_gap_from_quad (a := lowPrimeA prime79PlusRadius) (b :=
      lowPrimeB prime79PlusCap prime79PlusRadius +
        2 * (prime79PlusRadius : ℝ) ^ 2 * prime79PlusCreditR)
      hL (by norm_num only [prime79PlusRadius, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [prime79PlusLogLo, Rat.cast_div, Rat.cast_ofNat]) prime79Plus_log_bounds.1
      prime79Plus_coefficients.1 prime79Plus_coefficients.2
  · intro z
    dsimp only [finitePrincipalGap]
    rw [lowPrime_gap_quad (by norm_num only [prime79PlusRadius, Rat.cast_div, Rat.cast_ofNat]),
      lowPrime_gap_quad (by norm_num only [prime79PlusRadius, Rat.cast_div, Rat.cast_ofNat])]
    ring
  · exact prime79Plus_anchor

end PseudoPrime.LLS.PaperStatements
