/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FastArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CachedBounds
import PseudoPrime.Analysis.RationalHorner16Correct

/-! # Correctness of Horner-based endpoint evaluation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem endpoint_fast_power_eq (t q : ℚ) :
    endpointFastPower t q = endpointPowerApprox t q := by
  simp only [endpointFastPower, endpointPowerApprox, Analysis.rational_horner_real_eq,
    Analysis.rational_horner_phase_eq]

/-- The Horner-based rotated finite calculation equals the previously certified cached
calculation at every rational ordinate. Each exponential polynomial has exactly the same
value before the common rounding steps. -/
theorem endpoint_fast_rotated_eq (t : ℚ) : endpointFastRotated t = endpointCachedRotated t := by
  simp only [endpointFastRotated, endpointCachedRotated, Analysis.rational_horner_phase_eq,
    endpointFastFinite, endpointCachedFinite, endpoint_fast_power_eq]

/-- For `14 ≤ t ≤ 100`, a successful precise phase check bounds the difference between
normalized zeta and the Horner-based rational calculation by `3/2500000`. This combines the
analytic remainder with the equality of the two exact finite evaluators. -/
theorem abs_endpoint_fast_zeta (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    |RiemannXi.normalizedZeta t - ((endpointFastRotated t).1 : ℝ)| ≤ 3 / 2500000 := by
  rw [endpoint_fast_rotated_eq]
  exact abs_endpoint_cached_zeta t ht14 ht100 hcheck

/-- For a checked rational endpoint in `[14,100]`, a positive finite-value threshold of
`913/10000000` implies the normalized zeta margin `9/100000`. The threshold absorbs the
uniform analytic and computational error. -/
theorem endpoint_fast_positive_margin (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true)
    (hraw : (913 / 10000000 : ℚ) < (endpointFastRotated t).1) :
    (9 / 100000 : ℝ) < RiemannXi.normalizedZeta t := by
  have hr := (Rat.cast_lt (K := ℝ)).mpr hraw
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  have he := abs_le.mp (abs_endpoint_fast_zeta t ht14 ht100 hcheck)
  linarith only [hr, he.1]

/-- For a checked rational endpoint in `[14,100]`, a negative finite-value threshold of
`-913/10000000` implies the normalized zeta margin `-9/100000`. The uniform error estimate
transfers the exact rational comparison to the analytic value. -/
theorem endpoint_fast_negative_margin (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true)
    (hraw : (endpointFastRotated t).1 < (-913 / 10000000 : ℚ)) :
    RiemannXi.normalizedZeta t < -(9 / 100000 : ℝ) := by
  have hr := (Rat.cast_lt (K := ℝ)).mpr hraw
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at hr
  have he := abs_le.mp (abs_endpoint_fast_zeta t ht14 ht100 hcheck)
  linarith only [hr, he.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
