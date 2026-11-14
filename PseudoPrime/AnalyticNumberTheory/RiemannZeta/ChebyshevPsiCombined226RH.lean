/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombinedScaleRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiScale226
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Combined Chebyshev bound at logarithmic height 22.6 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and `L ≥ 113/5`, the chosen relative smoothing width gives
the displayed normalized Chebyshev error bound. The cutoff and endpoint
conditions are derived from elementary exponential estimates. -/
theorem psi_error_combined_at226 (hRH : RiemannHypothesis) {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let δ := q / s
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      s * δ / 2 + Real.log (2 * Real.pi) / s +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                  (2 * Real.pi) +
                2 / 5 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (Real.exp L * δ * s) := by
  dsimp only
  have hc := scale226_conditions hL
  have h := psi_error_combined_scaled hRH (Real.exp_pos L) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  simpa only [← Real.exp_half] using h

/-- Under RH and `L ≥ 113/5`, the normalized Chebyshev error is bounded by
the explicit smoothing envelope with `q = 5L/(6π)`. The nonpositive cutoff
correction is discarded after the chosen scale has been substituted. -/
theorem psi_error_envelope226 (hRH : RiemannHypothesis) {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let a := L / 2 - Real.log (5 * L / 6)
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) +
        1 / (q * Real.exp L) := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  have hs : s ≠ 0 := (Real.exp_pos _).ne'
  have hL0 : 0 < L := by linarith only [hL]
  have hpi := mul_inv_cancel₀ Real.pi_ne_zero
  have hsi := inv_mul_cancel₀ hs
  have halg : (2 / (q / s)) / (2 * Real.pi) = s / (5 * L / 6) := by
    dsimp only [q]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    linear_combination (s * (6 / 5 : ℝ) * L⁻¹) * hpi
  have hsq : s * (q / s) = q := by
    simp only [div_eq_mul_inv]
    linear_combination q * hsi
  have hrem : 1 / (Real.exp L * (q / s) * s) = 1 / (q * Real.exp L) := by
    have h : Real.exp L * (q / s) * s = q * Real.exp L := by
      simp only [div_eq_mul_inv]
      linear_combination (Real.exp L * q) * hsi
    rw [h]
  have hlog : Real.log (s / (5 * L / 6)) = L / 2 - Real.log (5 * L / 6) := by
    rw [Real.log_div hs (by linarith only [hL0] : (5 * L / 6 : ℝ) ≠ 0)]
    dsimp only [s]
    rw [Real.log_exp]
  have hc := scale226_conditions hL
  change 0 < q / s ∧ q / s ≤ 1 / 2 ∧ 40 ≤ 2 / (q / s) ∧ 1 < Real.exp L - Real.exp L * (q / s) at hc
  have hT0 : 0 < 2 / (q / s) := div_pos (by norm_num only) hc.1
  have ht1 : (1 / 15 : ℝ) / (2 / (q / s)) ≤ 3 / 8 := by
    apply (div_le_iff₀ hT0).2
    linarith only [hc.2.2.1]
  have ht2 := div_le_div_of_nonneg_right ht1 hT0.le
  have ht : -(3 / 8 : ℝ) / (2 / (q / s)) + 1 / (15 * (2 / (q / s)) ^ 2) ≤ 0 := by
    have he : (1 / 15 : ℝ) / (2 / (q / s)) / (2 / (q / s)) = 1 / (15 * (2 / (q / s)) ^ 2) := by ring
    rw [he] at ht2
    have hsub := sub_nonpos.mpr ht2
    convert hsub using 1
    ring
  have hpos : 0 ≤ 1 + q / s := by linarith only [hc.1]
  have hc' := mul_nonpos_of_nonneg_of_nonpos hpos ht
  have h := psi_error_combined_at226 hRH hL
  change
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      s * (q / s) / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) *
          (((Real.log ((2 / (q / s)) / (2 * Real.pi))) ^ 2 +
                    2 * Real.log ((2 / (q / s)) / (2 * Real.pi)) +
                    2) /
                  (2 * Real.pi) +
                2 / 5 -
              (3 / 8 : ℝ) / (2 / (q / s)) +
            1 / (15 * (2 / (q / s)) ^ 2)) +
        1 / (Real.exp L * (q / s) * s) at h
  rw [halg, hlog, hsq, hrem] at h
  rw [neg_div] at hc'
  nlinarith only [h, hc']

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
