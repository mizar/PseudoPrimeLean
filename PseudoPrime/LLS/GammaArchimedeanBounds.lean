/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorCentralBounds
public import PseudoPrime.LLS.GammaKernel
public import PseudoPrime.Analysis.ExponentialAbsoluteIntegral
public import PseudoPrime.LLS.MellinKernelGammaBounds
public import PseudoPrime.LLS.MellinKernelExplicitFormula
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Numerical archimedean integral for the Gamma Mellin kernel

A full complex gamma-factor bound and explicit Gamma decay give an integrable
rational envelope. Contour independence transfers the numerical constant fifteen
from the central line to every admissible right line.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At every height, the shifted Gamma kernel is bounded by 3exp(-3|t|/2).
Use Euler reflection, sqrt(2π)<3 and π>3. The explicit decay pairs with the
central gamma-factor norm estimate in the archimedean integral. -/
private theorem gamma_decay_numeric (t : ℝ) :
    ‖gammaMellinKernel.function (Complex.I * t)‖ ≤ 3 * Real.exp (-(3 / 2 * |t|)) := by
  have hg := Analysis.norm_Gamma_half_add_I_le_exp t
  have hs : Real.sqrt (2 * Real.pi) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by nlinarith only [Real.pi_lt_four]⟩
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (abs_nonneg t)
  have he : Real.exp (-|Real.pi * t| / 2) ≤ Real.exp (-(3 / 2 * |t|)) := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    apply Real.exp_le_exp.mpr
    linarith only [hp]
  change ‖Complex.Gamma (Complex.I * t + 1 / 2)‖ ≤ _
  rw [add_comm]
  exact hg.trans (mul_le_mul hs he (Real.exp_pos _).le (by norm_num only))

/-- For a≥0, the cubic Taylor lower bound for exp(3a/2) dominates
(10+a)(1+a²)/10. This converts exponential decay into an integrable rational
majorant without a numerically unspecified comparison constant. -/
private theorem exp_envelope_numeric {a : ℝ} (ha : 0 ≤ a) :
    (10 + a) * (1 + a ^ 2) ≤ 10 * Real.exp (3 / 2 * a) := by
  have he := Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 2) ha) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at he
  nlinarith only [he, ha, sq_nonneg a, mul_nonneg ha (sq_nonneg a)]

/-- For positive scale and any character, the central Gamma archimedean
integrand has norm at most 30/(1+t²). Its phase has norm one; the full complex
gamma-factor bound and kernel decay yield the rational envelope.
This is the pointwise input to the explicit integral constant. -/
theorem gamma_archimedean_integrand_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (t : ℝ) :
    ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      30 * (1 + t ^ 2)⁻¹ := by
  have hr : (Complex.I * (t : ℂ) + 1 / 2).re = (1 / 2 : ℝ) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re, zero_mul, mul_zero, sub_zero,
      zero_add]
  have hd :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_central_le_linear χ hr
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_ofNat_im, Complex.one_im, one_mul, zero_mul, zero_div, zero_add,
    add_zero] at hd
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
  have hm :=
    mul_le_mul hd (gamma_decay_numeric t) (norm_nonneg _)
      (by linarith only [abs_nonneg t] : 0 ≤ 10 + |t|)
  have he := exp_envelope_numeric (abs_nonneg t)
  rw [sq_abs] at he
  have hs : 0 < 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
  have hExp : Real.exp (3 / 2 * |t|) * Real.exp (-(3 / 2 * |t|)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(3 / 2 * |t|))).le
  rw [mul_assoc 10, hExp, mul_one] at hmul
  apply hm.trans
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  nlinarith only [hmul]

/-- For every character and positive scale, the normalized central Gamma
archimedean integral has norm at most fifteen. Integrate the majorant
30/(1+t²), whose integral is 30π, then divide by 2π.
The bound is independent of modulus, parity and scale. -/
theorem norm_gamma_central_integral_le_fifteen {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
      15 := by
  let F := fun t : ℝ ↦
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
      (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  have hfi : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_gammaFactor_power_line gammaMellinKernel χ (c := 0) (by norm_num only)
        (by linarith only [gammaMellinKernel.delta_pos]) (by norm_num only) hx
    simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using hi
  have hgi := integrable_inv_one_add_sq.const_mul (30 : ℝ)
  have hbound :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi (fun t ↦ gamma_archimedean_integrand_bound χ hx t))
  rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq] at hbound
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (30 * Real.pi) :=
      mul_le_mul_of_nonneg_left hbound
        (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))
    _ = 15 := by
      field_simp (discharger :=
        first
        | (norm_num only; done)
        | exact Real.pi_pos.ne')
      ring

/-- For scale x≥1 and an admissible nonnegative right line, the normalized
Gamma archimedean integral has norm at most fifteen. Move the integral to the
central line using the proved contour identity and apply its explicit bound.
This supplies a numerical archimedean constant to the fixed-kernel formula. -/
theorem norm_gamma_right_integral_le_fifteen {q : ℕ} (χ : DirichletCharacter ℂ q) {b x : ℝ}
    (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + gammaMellinKernel.delta) (hb2 : b ≤ 3 / 2) (hx : 1 ≤ x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((b : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function ((b : ℂ) + Complex.I * t) *
                (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      15 := by
  rw [MellinKernel.gammaIntegral_eq_central gammaMellinKernel χ hb hbK hb2 hx]
  exact norm_gamma_central_integral_le_fifteen χ (zero_lt_one.trans_le hx)

/-- Under GRH and primitive nonprincipal data, the Gamma arithmetic sum
differs from its completed residue, zero sum and left integral by at most fifteen,
for admissible contour lines and scale x≥1. Substitute the exact completed
formula and apply the explicit right archimedean bound.
The left integral and kernel-pole residue remain explicit for subsequent estimates. -/
theorem norm_gamma_completed_remainder_le_fifteen {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - gammaMellinKernel.delta < a) (hb : b ≤ 1 / 2 + gammaMellinKernel.delta)
    (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2) (hx : 1 ≤ x) (hal : a < -1 / 2) (hbr : 1 / 2 < b) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) -
          (MellinKernel.weightedResidue gammaMellinKernel
                (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
              (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                  (gammaMellinKernel.function ((a : ℂ) + Complex.I * t) *
                    (x : ℂ) ^ ((a : ℂ) + Complex.I * t))))‖ ≤
      15 := by
  have h :=
    MellinKernel.tsum_summand_eq_completed_residue_formula gammaMellinKernel hq hGRH hp hne hinv hab
      ha hb ha' hb' hx hal hbr
  dsimp only at h
  rw [h, add_sub_cancel_left]
  exact norm_gamma_right_integral_le_fifteen χ (by linarith only [hbr]) hb hb' hx

/-- For every character and positive scale, the central Gamma integrand is bounded
by 30exp(-7|t|/5). Bound 10+|t| by 10exp(|t|/10) and combine with Gamma decay.
The integrable exponential envelope gives a sharper archimedean constant. -/
theorem gamma_archimedean_integrand_exp_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (t : ℝ) :
    ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      30 * Real.exp (-(7 / 5) * |t|) := by
  have hr : (Complex.I * (t : ℂ) + 1 / 2).re = (1 / 2 : ℝ) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.div_ofNat_re, Complex.one_re, zero_mul, mul_zero, sub_zero,
      zero_add]
  have hd :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_central_le_linear χ hr
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.div_ofNat_im, Complex.one_im, one_mul, zero_mul, zero_div, zero_add,
    add_zero] at hd
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
  have hm :=
    mul_le_mul hd (gamma_decay_numeric t) (norm_nonneg _)
      (by linarith only [abs_nonneg t] : 0 ≤ 10 + |t|)
  have he : 10 + |t| ≤ 10 * Real.exp (|t| / 10) := by linarith only [Real.add_one_le_exp (|t| / 10)]
  have hm' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(3 / 2 * |t|))).le
  calc
    _ ≤ (10 + |t|) * (3 * Real.exp (-(3 / 2 * |t|))) := hm
    _ ≤ 30 * (Real.exp (|t| / 10) * Real.exp (-(3 / 2 * |t|))) := by nlinarith only [hm']
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- For every character and positive scale, the normalized central Gamma integral
has norm at most 64/9. Integrate the exponential envelope and use π>3.14.
The bound is uniform in modulus, parity and scale. -/
theorem norm_gamma_central_integral_le_sixty_four_ninths {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
      64 / 9 := by
  let F := fun t : ℝ ↦
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
      (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  have hfi : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_gammaFactor_power_line gammaMellinKernel χ (c := 0) (by norm_num only)
        (by linarith only [gammaMellinKernel.delta_pos]) (by norm_num only) hx
    simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using hi
  have hgi :=
    (Analysis.integrable_exp_neg_mul_abs (by norm_num only : (0 : ℝ) < 7 / 5)).const_mul (30 : ℝ)
  have hbound :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gamma_archimedean_integrand_exp_bound χ hx t))
  rw [MeasureTheory.integral_const_mul,
    Analysis.integral_exp_neg_mul_abs (by norm_num only : (0 : ℝ) < 7 / 5)] at hbound
  have hp : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hnum : (1 / (2 * Real.pi)) * (30 * (2 / (7 / 5))) ≤ (64 / 9 : ℝ) := by
    rw [one_div, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hp]
    nlinarith only [Real.pi_gt_d2]
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hp.le)]
  exact (mul_le_mul_of_nonneg_left hbound (div_nonneg zero_le_one hp.le)).trans hnum

/-- For x≥1 and an admissible nonnegative right line, the normalized Gamma integral
has norm at most 64/9. Transfer to the central line by contour independence.
This supplies the improved archimedean constant for the completed formula. -/
theorem norm_gamma_right_integral_le_sixty_four_ninths {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + gammaMellinKernel.delta) (hb2 : b ≤ 3 / 2)
    (hx : 1 ≤ x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((b : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function ((b : ℂ) + Complex.I * t) *
                (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      64 / 9 := by
  rw [MellinKernel.gammaIntegral_eq_central gammaMellinKernel χ hb hbK hb2 hx]
  exact norm_gamma_central_integral_le_sixty_four_ninths χ (zero_lt_one.trans_le hx)

/-- Under GRH and primitive nonprincipal data, the completed Gamma arithmetic
formula has archimedean remainder at most 64/9 on admissible contour lines.
Substitute the exact formula and apply the right-line integral bound.
The residue, zero sum and left integral remain explicit for later estimates. -/
theorem norm_gamma_completed_remainder_le_sixty_four_ninths {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - gammaMellinKernel.delta < a) (hb : b ≤ 1 / 2 + gammaMellinKernel.delta)
    (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2) (hx : 1 ≤ x) (hal : a < -1 / 2) (hbr : 1 / 2 < b) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) -
          (MellinKernel.weightedResidue gammaMellinKernel
                (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
              (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                  (gammaMellinKernel.function ((a : ℂ) + Complex.I * t) *
                    (x : ℂ) ^ ((a : ℂ) + Complex.I * t))))‖ ≤
      64 / 9 := by
  have h :=
    MellinKernel.tsum_summand_eq_completed_residue_formula gammaMellinKernel hq hGRH hp hne hinv hab
      ha hb ha' hb' hx hal hbr
  dsimp only at h
  rw [h, add_sub_cancel_left]
  exact norm_gamma_right_integral_le_sixty_four_ninths χ (by linarith only [hbr]) hb hb' hx

end PseudoPrime.LLS.PaperStatements
