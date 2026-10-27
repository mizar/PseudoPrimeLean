/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerCorrectedPhase
public import PseudoPrime.Analysis.GammaEulerApproximationBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Kernel-certified error for the order-256 corrected Euler approximation -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: an order n and a proposed square root k.
Output: the rational corrected half-argument mass with n^(1/2) replaced by k.
Role: check the real error allowance using exact rational arithmetic. -/
def gammaEulerHalfRationalMass (n k : ℕ) : ℚ :=
  ((k : ℚ) * n.factorial / ∏ j ∈ Finset.range (n + 1), (1 / 2 + (j : ℚ))) *
    (1 + (1 / 2 : ℚ) * (1 / 2 + 1) * n / (2 * (n + 1 + 1 / 2) * (n + 1 + (1 / 2 + 1))))

/-- Input: a nonzero order whose real half power is the natural number k.
Claim: the corrected half-argument product equals the rational mass.
Proof: use the rational multiplier formula and commute finite products with casts.
Role: transfer kernel-checked rational inequalities to the analytic error. -/
theorem gammaEulerCorrected_half_eq_rational {n k : ℕ} (hn : n ≠ 0)
    (hp : (n : ℝ) ^ (1 / 2 : ℝ) = k) :
    gammaEulerCorrectedApprox (1 / 2 : ℂ) n = (gammaEulerHalfRationalMass n k : ℂ) := by
  rw [gammaEulerCorrectedApprox_factor (by norm_num only) (by norm_num only) hn]
  have he :
    Complex.GammaSeq (1 / 2 : ℂ) n =
      ((k : ℝ) * n.factorial / ∏ j ∈ Finset.range (n + 1), (1 / 2 + (j : ℝ)) : ℝ) := by
    have h := GammaSeq_ofReal_eq_realApprox (1 / 2) n
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, gammaEulerRealApprox, hp] at h
    exact h
  rw [he]
  simp only [gammaEulerHalfRationalMass, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_prod, Rat.cast_add, Rat.cast_ofNat, Rat.cast_one, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_prod, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_ofNat]

/-- Claim: the rational corrected mass at order 256 is at least 1.772415.
Proof: kernel evaluation of the factorial and 257 rational factors.
Role: certify the approximation allowance without floating-point evaluation. -/
theorem gammaEulerHalfRationalMass_256_lower :
    (1772415 / 1000000 : ℚ) ≤ gammaEulerHalfRationalMass 256 16 := by decide +kernel

/-- Claim: the exact half-argument error at order 256 is at most 1/25000.
Proof: combine the kernel-checked mass with the proved numerical upper bound for pi.
Role: supply a small uniform error for finite phase certification. -/
theorem gammaEulerCorrectedHalfError_256_le :
    gammaEulerCorrectedHalfError 256 ≤ (1 / 25000 : ℝ) := by
  have hp : (256 : ℝ) ^ (1 / 2 : ℝ) = 16 := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have hm := gammaEulerCorrected_half_eq_rational (by decide : 256 ≠ 0) hp
  have hl : (1772415 / 1000000 : ℝ) ≤ (gammaEulerHalfRationalMass 256 16 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr gammaEulerHalfRationalMass_256_lower
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have hs : Real.sqrt Real.pi ≤ (1772454 / 1000000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num only
    · linarith only [Real.pi_lt_d6]
  rw [gammaEulerCorrectedHalfError, hm, ← Complex.ofReal_ratCast, Complex.ofReal_re]
  linarith only [hl, hs]

/-- Input: any real ordinate. Claim: the order-256 corrected error is at most 1/25000.
Proof: specialize the exact positive error mass bound.
Role: replace long uncorrected Euler products with a shorter certified approximation. -/
theorem norm_Gamma_half_sub_corrected256_le (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) -
          gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) 256‖ ≤
      (1 / 25000 : ℝ) := by
  exact
    (norm_Gamma_half_sub_corrected_le t (by decide : 256 ≠ 0)).trans
      gammaEulerCorrectedHalfError_256_le

/-- Input: a positive scale and any real ordinate.
Claim: the corrected order-256 phase plus 1/25000 bounds the actual Gamma phase.
Proof: combine phase norm invariance with the certified scalar allowance.
Role: connect the numerical certificate to a continuous spectral majorant. -/
theorem neg_re_Gamma_phase_le_corrected256 {x : ℝ} (hx : 0 < x) (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      -(gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * t) 256 *
              (x : ℂ) ^ (Complex.I * t)).re +
        (1 / 25000 : ℝ) := by
  exact
    (neg_re_Gamma_phase_le_corrected hx t (by decide : 256 ≠ 0)).trans
      (add_le_add_right gammaEulerCorrectedHalfError_256_le _)

end PseudoPrime.Analysis
