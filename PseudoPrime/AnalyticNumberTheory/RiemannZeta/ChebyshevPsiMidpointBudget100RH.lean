/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiHeadBudget100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadMidpointRH

/-! # ψ error from midpoint values of the signed height-100 zero sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the height-100 zero count, bounds on both midpoint zero
sums and on their weighted distance sum give a ψ error estimate. Apply
midpoint quadrature on both smoothing intervals and combine the remaining
zeros using the height-100 budget. -/
theorem psi_error_midpoint_budget100 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    {T x h D C M : ℝ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hM : (∑ ρ ∈ zerosUpTo 100, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) ≤ M)
    (hlo :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((x - h + x) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C)
    (hhi :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((x + (x + h)) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) + (C + M * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  have hm0 : 0 ≤ M :=
    (Finset.sum_nonneg (fun ρ hρ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).trans hM
  have hx0 : 0 < x - h := zero_lt_one.trans hx
  have hxa : 0 < x := by linarith only [hx0, hh]
  have hlo' :=
    zero_head_integral_le_midpoint hRH (show (0 : ℝ) ≤ 100 by norm_num only) hx0
      (show x - h ≤ x by linarith only [hh]) hM hlo
  have hhi' :=
    zero_head_integral_le_midpoint hRH (show (0 : ℝ) ≤ 100 by norm_num only) hxa
      (show x ≤ x + h by linarith only [hh]) hM hhi
  have hwlo : x - (x - h) = h := by ring
  have hwhi : x + h - x = h := by ring
  rw [hwlo] at hlo'
  rw [hwhi] at hhi'
  have hp :=
    Real.rpow_le_rpow_of_nonpos hx0 (show x - h ≤ x by linarith only [hh])
      (show (-(3 / 2 : ℝ)) ≤ 0 by norm_num only)
  have hm := mul_le_mul_of_nonneg_left hp hm0
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg h)
  apply psi_error_head_budget100 hRH h100 hT hh hx hD hsqrt htail
  · simpa only [mul_div_assoc] using hlo'
  · have hh' : 0 ≤ h := hh.le
    have hh'' := mul_le_mul_of_nonneg_left hm' hh'
    simp only [mul_div_assoc] at hhi' ⊢
    nlinarith only [hhi', hh'']

/-- Under RH and a count of 58 zeros through height 100, the midpoint ψ
estimate holds with the explicit distance-sum bound 5829. This eliminates
the separate weighted-distance hypothesis without any ordinate table. -/
theorem psi_error_midpoint_count100 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    {T x h D C : ℝ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((x - h + x) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C)
    (hhi :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((x + (x + h)) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) + (C + 5829 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  have hm := zero_head_distance_le_count hRH (show (0 : ℝ) ≤ 100 by norm_num only)
  rw [h100] at hm
  norm_num only at hm
  exact psi_error_midpoint_budget100 hRH h100 hT hh hx hD hsqrt htail hm hlo hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
