/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombined100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiScale20

/-! # Conditional normalized ψ envelope above logarithmic height 20 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the height-100 count and reciprocal head bounds yield the
displayed normalized ψ envelope for `L ≥ 20`, using smoothing scale `L/4`.
The scale conditions and the nonpositive cutoff correction are discharged. -/
theorem psi_error_envelope20 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    (hhead : zeroReciprocalSum 100 ≤ 11846 / 10000) {L : ℝ} (hL : 20 ≤ L) :
    let s := Real.exp (L / 2)
    let q := L / 4
    let a := L / 2 - Real.log (Real.pi * L / 4)
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) +
        1 / (q * Real.exp L) := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := L / 4
  change
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) *
          (((L / 2 - Real.log (Real.pi * L / 4)) ^ 2 + 2 * (L / 2 - Real.log (Real.pi * L / 4)) +
                2) /
              (2 * Real.pi) +
            1 / 25) +
        1 / (q * Real.exp L)
  have hs : s ≠ 0 := (Real.exp_pos _).ne'
  have hL0 : 0 < L := by linarith only [hL]
  have hsi := inv_mul_cancel₀ hs
  have halg : (2 / (q / s)) / (2 * Real.pi) = s / (Real.pi * L / 4) := by
    dsimp only [q]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  have hsq : s * (q / s) = q := by
    simp only [div_eq_mul_inv]
    linear_combination q * hsi
  have hrem : 1 / (Real.exp L * (q / s) * s) = 1 / (q * Real.exp L) := by
    have h : Real.exp L * (q / s) * s = q * Real.exp L := by
      simp only [div_eq_mul_inv]
      linear_combination (Real.exp L * q) * hsi
    rw [h]
  have hlog : Real.log (s / (Real.pi * L / 4)) = L / 2 - Real.log (Real.pi * L / 4) := by
    rw [Real.log_div hs
        (div_ne_zero (mul_ne_zero Real.pi_ne_zero hL0.ne') (by norm_num only : (4 : ℝ) ≠ 0))]
    dsimp only [s]
    rw [Real.log_exp]
  have hc := scale20_conditions hL
  change 0 < q / s ∧ q / s ≤ 1 / 2 ∧ 100 ≤ 2 / (q / s) ∧ 1 < Real.exp L - Real.exp L * (q / s) at hc
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
  have h :=
    psi_error_combined100_scaled hRH h100 hhead (Real.exp_pos L) hc.1 hc.2.1 hc.2.2.2 hc.2.2.1
  rw [← Real.exp_half] at h
  change
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      s * (q / s) / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) *
          (((Real.log ((2 / (q / s)) / (2 * Real.pi))) ^ 2 +
                    2 * Real.log ((2 / (q / s)) / (2 * Real.pi)) +
                    2) /
                  (2 * Real.pi) +
                1 / 25 -
              (3 / 8 : ℝ) / (2 / (q / s)) +
            1 / (15 * (2 / (q / s)) ^ 2)) +
        1 / (Real.exp L * (q / s) * s) at h
  rw [halg, hlog, hsq, hrem] at h
  rw [neg_div] at hc'
  nlinarith only [h, hc']

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
