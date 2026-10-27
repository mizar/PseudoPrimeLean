/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerCorrectedApproximation
public import PseudoPrime.Analysis.GammaEulerPhaseApproximation

/-! # Gamma phase comparison with a positive corrected Euler approximation -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a natural order. Output: sqrt(pi) minus the real corrected product at 1/2.
Role: supply the exact scalar error allowance, independent of ordinate and phase scale. -/
noncomputable def gammaEulerCorrectedHalfError (n : ℕ) : ℝ :=
  Real.sqrt Real.pi - (gammaEulerCorrectedApprox (1 / 2 : ℂ) n).re

/-- Input: any real ordinate and a nonzero order.
Claim: the corrected Gamma error is at most gammaEulerCorrectedHalfError.
Proof: specialize the positive integral error bound to real part 1/2.
Role: reduce complex approximation certification to one scalar product. -/
theorem norm_Gamma_half_sub_corrected_le (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) -
          gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) n‖ ≤
      gammaEulerCorrectedHalfError n := by
  have hr : ((1 / 2 : ℂ) + Complex.I * t).re = (1 / 2 : ℝ) := by
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero]
  have h :=
    norm_Gamma_sub_corrected_le_real_gap (s := (1 / 2 : ℂ) + Complex.I * t)
      (by
        rw [hr]; norm_num only)
      hn
  rw [hr, Real.Gamma_one_half_eq, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  exact h

/-- Input: a positive scale, any ordinate and a nonzero order.
Claim: the corrected phase plus the scalar error bounds the actual Gamma phase.
Proof: the imaginary power preserves the error norm.
Role: certify a spectral majorant with corrected finite products. -/
theorem neg_re_Gamma_phase_le_corrected {x : ℝ} (hx : 0 < x) (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      -(gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) n * (x : ℂ) ^ (Complex.I * t)).re +
        gammaEulerCorrectedHalfError n := by
  exact
    (neg_re_phase_le_approx_add_error (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t))
          (gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) n) hx t).trans
      (add_le_add_right (norm_Gamma_half_sub_corrected_le t hn) _)

end PseudoPrime.Analysis
