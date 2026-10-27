/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RoundedEulerProduct
public import PseudoPrime.Analysis.HalfLinePhaseNormalization

/-! # Certified Gamma phases from rounded finite Euler products -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a complex exponent. Output: 256^s/s times the finite rational correction factor.
Role: separate the transcendental phase from the contractive rational Euler product. -/
noncomputable def gammaEuler256Multiplier (s : ℂ) : ℂ :=
  (256 : ℂ) ^ s / s * (1 + s * (s + 1) * 256 / (2 * (256 + 1 + s) * (256 + 1 + (s + 1))))

/-- Input: s and s+1 different from zero.
Claim: the corrected order-256 approximation is its multiplier times the normalized product.
Proof: combine the finite Gamma recurrence with the factorial-product identity.
Role: use a stable product evaluator without changing the analytic approximation. -/
theorem gammaEulerCorrected256_eq_normalized {s : ℂ} (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    gammaEulerCorrectedApprox s 256 = gammaEuler256Multiplier s * eulerUnitProduct s 256 := by
  rw [gammaEulerCorrectedApprox_factor hs hs1 (by decide), GammaSeq_eq_eulerUnitProduct s hs]
  dsimp only [gammaEuler256Multiplier]
  norm_num only [Nat.cast_ofNat]
  ring

/-- Input: Re(s)=1/2 and |Im(s)|<=5.
Claim: the normalized corrected multiplier has norm at most 64.
Proof: bound the power-over-s factor by 32 and the rational correction by two.
Role: transfer bounded product-rounding errors to the low-frequency Gamma phase. -/
theorem norm_gammaEuler256Multiplier_le {s : ℂ} (hs : s.re = 1 / 2) (ht : |s.im| ≤ 5) :
    ‖gammaEuler256Multiplier s‖ ≤ 64 := by
  have hr := Complex.re_le_norm s
  rw [hs] at hr
  have hpref : ‖(256 : ℂ) ^ s / s‖ ≤ 32 := by
    have hg : ‖(256 : ℂ) ^ s‖ = 16 := by
      change ‖((256 : ℝ) : ℂ) ^ s‖ = 16
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num only), hs, ← Real.sqrt_eq_rpow]
      exact (Real.sqrt_eq_iff_eq_sq (by norm_num only) (by norm_num only)).mpr (by norm_num only)
    rw [norm_div, hg]
    exact (div_le_iff₀ (by linarith only [hr] : 0 < ‖s‖)).mpr (by linarith only [hr])
  have hsn : ‖s‖ ≤ 6 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hs, abs_of_pos (by norm_num only : (0 : ℝ) < 1 / 2)] at h
    linarith only [h, ht]
  have hs1n : ‖s + 1‖ ≤ 7 := by
    have h := norm_add_le s 1
    rw [norm_one] at h
    linarith only [h, hsn]
  have hd1 : (256 : ℝ) ≤ ‖(256 + 1 : ℂ) + s‖ := by
    have h := Complex.re_le_norm ((256 + 1 : ℂ) + s)
    norm_num only [Complex.add_re, Complex.re_ofNat, Complex.one_re, hs] at h ⊢
    linarith only [h]
  have hd2 : (256 : ℝ) ≤ ‖(256 + 1 : ℂ) + (s + 1)‖ := by
    have h := Complex.re_le_norm ((256 + 1 : ℂ) + (s + 1))
    norm_num only [Complex.add_re, Complex.re_ofNat, Complex.one_re, hs] at h ⊢
    linarith only [h]
  have hden : (131072 : ℝ) ≤ ‖(2 : ℂ) * (256 + 1 + s) * (256 + 1 + (s + 1))‖ := by
    rw [norm_mul, norm_mul]
    norm_num only [Complex.norm_ofNat]
    norm_num only at hd1 hd2
    have h := mul_le_mul hd1 hd2 (by norm_num only : (0 : ℝ) ≤ 256) (norm_nonneg _)
    nlinarith only [h]
  have hnum : ‖s * (s + 1) * (256 : ℂ)‖ ≤ 10752 := by
    rw [norm_mul, norm_mul]
    norm_num only [Complex.norm_ofNat]
    have h := mul_le_mul hsn hs1n (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 6)
    nlinarith only [h]
  have hc : ‖s * (s + 1) * 256 / (2 * (256 + 1 + s) * (256 + 1 + (s + 1)))‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one (by linarith only [hden])).mpr (by linarith only [hnum, hden])
  have hsum := norm_add_le (1 : ℂ) (s * (s + 1) * 256 / (2 * (256 + 1 + s) * (256 + 1 + (s + 1))))
  rw [norm_one] at hsum
  rw [gammaEuler256Multiplier, norm_mul]
  have hmul :=
    mul_le_mul hpref (hsum.trans (add_le_add_right hc 1)) (norm_nonneg _)
      (by norm_num only : (0 : ℝ) ≤ 32)
  norm_num only at hmul ⊢
  exact hmul

/-- Input: a grid denominator and rational ordinate.
Output: the analytic multiplier times the executable rounded order-256 product.
Role: approximate Gamma using bounded-denominator arithmetic and one phase multiplier. -/
noncomputable def roundedGamma256 (G : ℕ) (t : ℚ) : ℂ :=
  gammaEuler256Multiplier ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
    rationalComplexCast (roundedEulerUnitProduct G t 256)

/-- Input: a positive grid denominator and rational ordinate of absolute value at most five.
Claim: rounding the corrected approximation costs at most 32768/G in norm.
Proof: multiply the product error 512/G by the multiplier bound 64.
Role: quantify every arithmetic rounding operation in node evaluation. -/
theorem norm_corrected256_sub_rounded_le {G : ℕ} (hG : 0 < G) (t : ℚ) (ht : |(t : ℝ)| ≤ 5) :
    ‖gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) 256 - roundedGamma256 G t‖ ≤
      32768 / (G : ℝ) := by
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  have hs : s.re = (1 / 2 : ℝ) := by
    norm_num only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul, mul_zero,
      sub_zero, add_zero]
  have hsn : s ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    rw [hs, Complex.zero_re] at h
    norm_num only at h
  have hs1n : s + 1 ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    rw [Complex.add_re, hs, Complex.one_re, Complex.zero_re] at h
    norm_num only at h
  have hi : |s.im| ≤ 5 := by
    norm_num only [s, Complex.add_im, Complex.div_ofNat_im, Complex.one_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul, one_mul,
      mul_zero, add_zero, zero_add]
    exact ht
  have he :
    gammaEulerCorrectedApprox s 256 - roundedGamma256 G t =
      gammaEuler256Multiplier s *
        (eulerUnitProduct s 256 - rationalComplexCast (roundedEulerUnitProduct G t 256)) := by
    rw [gammaEulerCorrected256_eq_normalized hsn hs1n, roundedGamma256]
    ring
  change ‖gammaEulerCorrectedApprox s 256 - roundedGamma256 G t‖ ≤ _
  rw [he, norm_mul, norm_sub_rev]
  have h :=
    mul_le_mul (norm_gammaEuler256Multiplier_le hs hi) (roundedEulerUnitProduct_error hG t 256)
      (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 64)
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1
  ring

/-- Input: a positive grid denominator and rational ordinate in [-5,5].
Claim: the rounded approximation error for actual Gamma is at most 1/25000+32768/G.
Proof: add the proved corrected Euler error and the rounded product error.
Role: certify node values without an unproved special-function oracle. -/
theorem norm_Gamma_sub_roundedGamma256_le {G : ℕ} (hG : 0 < G) (t : ℚ) (ht : |(t : ℝ)| ≤ 5) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) - roundedGamma256 G t‖ ≤
      (1 / 25000 : ℝ) + 32768 / (G : ℝ) := by
  have ha :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) -
          gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) 256‖ ≤
      (1 / 25000 : ℝ) := by
    simpa only [Complex.ofReal_ratCast] using norm_Gamma_half_sub_corrected256_le (t : ℝ)
  exact
    (norm_sub_le_norm_sub_add_norm_sub _
          (gammaEulerCorrectedApprox ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) 256) _).trans
      (add_le_add ha (norm_corrected256_sub_rounded_le hG t ht))

/-- Input: a positive phase scale, positive grid denominator and rational ordinate in [-5,5].
Claim: the rounded phase plus 1/25000+32768/G bounds the actual negative Gamma phase.
Proof: imaginary powers preserve the norm of the approximation error.
Role: provide rigorously rounded inputs to a low-frequency spectral certificate. -/
theorem neg_re_Gamma_phase_le_roundedGamma256 {x : ℝ} (hx : 0 < x) {G : ℕ} (hG : 0 < G) (t : ℚ)
    (ht : |(t : ℝ)| ≤ 5) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ) ^ (Complex.I * (t : ℂ))).re ≤
      -(roundedGamma256 G t * (x : ℂ) ^ (Complex.I * (t : ℂ))).re +
        ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) := by
  have h :=
    neg_re_phase_le_approx_add_error (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)))
      (roundedGamma256 G t) hx (t : ℝ)
  simp only [Complex.ofReal_ratCast] at h
  exact h.trans (add_le_add_right (norm_Gamma_sub_roundedGamma256_le hG t ht) _)

/-- Input: a rational ordinate in [-5,5].
Claim: grid denominator 10^12 gives a uniform Gamma error at most 40033/10^9.
Proof: specialize the general bound and compare rational constants.
Role: fix a practical precision without generating a large finite payload. -/
theorem norm_Gamma_sub_roundedGamma256_grid12_le (t : ℚ) (ht : |(t : ℝ)| ≤ 5) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) - roundedGamma256 (10 ^ 12) t‖ ≤
      (40033 / 1000000000 : ℝ) := by
  exact
    (norm_Gamma_sub_roundedGamma256_le (by norm_num only : 0 < 10 ^ 12) t ht).trans
      (by norm_num only)

/-- Claim: the actual Gamma value at ordinate 109/50 is within 40033/10^9 of the displayed
rational pair times the analytic multiplier.
Proof: use the kernel-checked executable product and the uniform error theorem.
Role: connect the representative arithmetic certificate to its actual Gamma value. -/
theorem norm_Gamma_at_109_div_50_sub_grid12_node_le :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (109 / 50)) -
          gammaEuler256Multiplier ((1 / 2 : ℂ) + Complex.I * (109 / 50)) *
            rationalComplexCast
              ((2485413517 / 1000000000000 : ℚ), (11230133857 / 1000000000000 : ℚ))‖ ≤
      (40033 / 1000000000 : ℝ) := by
  have h :=
    norm_Gamma_sub_roundedGamma256_grid12_le (109 / 50)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat, abs_of_pos])
  rw [roundedGamma256, roundedEulerUnitProduct_grid12_at_109_div_50] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Input: a grid denominator and rational ordinate.
Output: the rational complex correction and rounded product, excluding the exponential phase.
Role: leave a single imaginary exponential for interval certification. -/
noncomputable def roundedGamma256Coefficient (G : ℕ) (t : ℚ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
  16 / s * (1 + s * (s + 1) * 256 / (2 * (256 + 1 + s) * (256 + 1 + (s + 1)))) *
    rationalComplexCast (roundedEulerUnitProduct G t 256)

/-- Input: a positive phase scale, grid denominator and rational ordinate.
Claim: the rounded Gamma phase equals its rational coefficient times exp(i*t*log(256*x)).
Proof: combine the half-line power and the imaginary phase, then rearrange factors.
Role: isolate the remaining transcendental node calculation. -/
theorem roundedGamma256_phase_eq {x : ℝ} (hx : 0 < x) (G : ℕ) (t : ℚ) :
    roundedGamma256 G t * (x : ℂ) ^ (Complex.I * (t : ℂ)) =
      roundedGamma256Coefficient G t *
        Complex.exp (Complex.I * (((t : ℝ) * Real.log (256 * x) : ℝ) : ℂ)) := by
  have hsqrt : Real.sqrt (256 : ℝ) = 16 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num only) (by norm_num only)).mpr (by norm_num only)
  have he := halfLine_cpow_mul_phase (by norm_num only : (0 : ℝ) < 256) hx (t : ℝ)
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_ratCast, hsqrt] at he
  dsimp only [roundedGamma256, roundedGamma256Coefficient, gammaEuler256Multiplier]
  have hmul :=
    congrArg
      (fun z : ℂ ↦
        z / ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) *
          (1 +
            ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * ((1 / 2 : ℂ) + Complex.I * (t : ℂ) + 1) * 256 /
              (2 * (256 + 1 + ((1 / 2 : ℂ) + Complex.I * (t : ℂ))) *
                (256 + 1 + (((1 / 2 : ℂ) + Complex.I * (t : ℂ)) + 1)))) *
          rationalComplexCast (roundedEulerUnitProduct G t 256))
      he
  convert hmul using 1 <;> ring

/-- Input: a positive scale, positive grid denominator and rational ordinate in [-5,5].
Claim: the explicit coefficient phase plus 1/25000+32768/G bounds the actual Gamma phase.
Proof: rewrite the certified rounded approximation using the single exponential identity.
Role: provide a compact arithmetic and phase interface for low-frequency certification. -/
theorem neg_re_Gamma_phase_le_roundedCoefficient {x : ℝ} (hx : 0 < x) {G : ℕ} (hG : 0 < G) (t : ℚ)
    (ht : |(t : ℝ)| ≤ 5) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ) ^ (Complex.I * (t : ℂ))).re ≤
      -(roundedGamma256Coefficient G t *
              Complex.exp (Complex.I * (((t : ℝ) * Real.log (256 * x) : ℝ) : ℂ))).re +
        ((1 / 25000 : ℝ) + 32768 / (G : ℝ)) := by
  have h := neg_re_Gamma_phase_le_roundedGamma256 hx hG t ht
  rw [roundedGamma256_phase_eq hx G t] at h
  exact h

end PseudoPrime.Analysis
