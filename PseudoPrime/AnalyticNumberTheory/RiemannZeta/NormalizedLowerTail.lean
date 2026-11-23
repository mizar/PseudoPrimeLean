/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbove100RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail

/-! # Normalized zero tail for the lower Chebyshev bound -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On the lower interval the tail coefficient needs no right-endpoint enlargement. -/
private theorem lower_tail_coefficient {a x d : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hax : a ≤ x)
    (hd : 0 < d) (hw : x - a = x * d) :
    (x ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (x - a) ≤ Real.sqrt x * (2 / d) := by
  have hp := Real.rpow_le_rpow ha hax (by norm_num only : (0 : ℝ) ≤ 3 / 2)
  have he : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [he] at hp ⊢
  rw [hw, div_le_iff₀ (mul_pos hx hd)]
  have hc := div_mul_cancel₀ (2 : ℝ) hd.ne'
  linear_combination hp - x * Real.sqrt x * hc

/-- At the lower midpoint the normalized tail is bounded by the combined height-100 budget. -/
theorem normalized_lower_tail (hRH : RiemannHypothesis) (hc : zeroCount 100 = 58) {a x d T : ℝ}
    (ha : 0 ≤ a) (hx : 0 < x) (hax : a ≤ x) (hd : 0 < d) (hw : x - a = x * d) (hcut : 2 / d = T)
    (hT : 100 ≤ T) :
    (Real.sqrt x * (zeroReciprocalSum T - zeroReciprocalSum 100) +
          (x ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (x - a) * ordinateTail T) /
        Real.sqrt x ≤
      ((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) / (2 * Real.pi) -
          143 / 125 -
          (3 / 8 : ℝ) / T +
        1 / (15 * T ^ 2) := by
  have hu : 0 ≤ ordinateTail T := by
    rw [ordinateTail_eq]
    exact tsum_nonneg (fun ρ => (ordinateTailWeight_bound hRH T ρ).1)
  have h := lower_tail_coefficient ha hx hax hd hw
  rw [hcut] at h
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mpr
  have hb := mul_le_mul_of_nonneg_right (combined_zero_above100 hRH hc hT) (Real.sqrt_nonneg x)
  nlinarith only [hb, mul_le_mul_of_nonneg_right h hu]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
