/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScaleError
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiSharpRH

/-! # Normalized Chebyshev bound with refined zero sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem psi_error_scaled_raw_065 {x h T δ : ℝ} (hx0 : 0 < x) (hh : 0 < h) (hT : 1000 ≤ T)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 2) (hwidth : h = x * δ)
    (hb :
      |Chebyshev.psi x - x| ≤
        h / 2 + Real.log (2 * Real.pi) +
          Real.sqrt (x + h) * ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
          ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
          1 / h) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt x * (1 + δ / 2)) *
          ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
        (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  have hp := scale_power_bounds hx0 hδ hδ2
  rw [← hwidth] at hp
  have ht0 : 0 ≤ T := by linarith only [hT]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have hc : 0 ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20 := by
    have h :=
      div_nonneg (sq_nonneg (Real.log (T / (2 * Real.pi))))
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num only) Real.pi_pos.le)
    linarith only [h]
  have hf : 0 ≤ Real.log T / (Real.pi * T) := div_nonneg hlog (mul_nonneg Real.pi_pos.le ht0)
  have hl := mul_le_mul_of_nonneg_right hp.1 hc
  have hhpow :
    (x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ) ≤ x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ) :=
    add_le_add hp.2 le_rfl
  have hhdiv := div_le_div_of_nonneg_right hhpow hh.le
  have hhigh := mul_le_mul_of_nonneg_right hhdiv hf
  linarith only [hb, hl, hhigh]

private theorem psi_error_normalized_raw_065 {x h δ : ℝ} (hx0 : 0 < x) (hδ : 0 < δ)
    (hwidth : h = x * δ)
    (hb :
      |Chebyshev.psi x - x| ≤
        h / 2 + Real.log (2 * Real.pi) +
          (Real.sqrt x * (1 + δ / 2)) *
            ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
          (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h *
            (Real.log (2 / δ) / (Real.pi * (2 / δ))) +
          1 / h) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ / 2) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hxp : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hr := Real.rpow_add hx0 (1 : ℝ) (1 / 2 : ℝ)
    convert hr using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hhdiv := div_le_div_of_nonneg_right hb hs.le
  have heq :
    (h / 2 + Real.log (2 * Real.pi) +
          (Real.sqrt x * (1 + δ / 2)) *
            ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
          (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h *
            (Real.log (2 / δ) / (Real.pi * (2 / δ))) +
          1 / h) /
        Real.sqrt x =
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ / 2) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * Real.sqrt x) := by
    have hxne : x ≠ 0 := hx0.ne'
    have hdne : δ ≠ 0 := hδ.ne'
    have hsne : Real.sqrt x ≠ 0 := hs.ne'
    have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [hxp, hwidth]
    field_simp
    ring
  rw [heq] at hhdiv
  exact hhdiv

/-- Under RH, for positive width `h = xδ`, `δ ≤ 1/2`, and cutoff `2/δ ≥ 1000`,
the normalized Chebyshev error obeys the displayed bound. The reciprocal-zero
sum improvement permits the constant `13/20` in the low-zero term. -/
theorem psi_error_normalized_065 (hRH : RiemannHypothesis) {x h δ : ℝ} (hx0 : 0 < x) (hh : 0 < h)
    (hx : 1 < x - h) (hT : 1000 ≤ 2 / δ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hwidth : h = x * δ) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ / 2) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
        (1 + δ) * Real.log (2 / δ) / Real.pi +
        1 / (h * Real.sqrt x) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hc : (4 / 5 : ℝ) - 1 / (2 * Real.pi) ≤ 13 / 20 := by
    have hpi : Real.pi < (22 / 7 : ℝ) := by
      have h := Real.pi_lt_d4
      norm_num only at h ⊢
      linarith only [h]
    have hi' : (7 / 44 : ℝ) ≤ 1 / (2 * Real.pi) := by
      apply (le_div_iff₀ hp).2
      linarith only [hpi]
    linarith only [hi']
  have hb := Arithmetic.psi_error_sharp_of_RH hRH hT hh hx
  have hm := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg (x + h))
  have hb' :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * ((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 13 / 20) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log (2 / δ) / (Real.pi * (2 / δ))) +
        1 / h := by
    nlinarith only [hb, hm]
  exact
    psi_error_normalized_raw_065 hx0 hδ hwidth
      (psi_error_scaled_raw_065 hx0 hh hT hδ.le hδ2 hwidth hb')

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
