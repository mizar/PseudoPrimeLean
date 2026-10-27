/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianKernel
public import PseudoPrime.LLS.GammaArchimedeanBounds

/-! # Explicit Gaussian archimedean contour bounds

Bound the actual Gaussian integrands using their exponential multiplier.
The central bound 64/9 transfers to every admissible right line and the completed formula.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every vertical line c and complex factors D,p, the actual Gaussian
integrand norm is at most exp(c²/4) times the corresponding Gamma integrand norm.
An exact factorization and the proved multiplier bound justify this pointwise comparison. -/
theorem gaussian_kernel_integrand_norm_le (c t : ℝ) (D p : ℂ) :
    ‖D * (gaussianGammaMellinKernel.function ((c : ℂ) + Complex.I * t) * p)‖ ≤
      Real.exp (c ^ 2 / 4) * ‖D * (gammaMellinKernel.function ((c : ℂ) + Complex.I * t) * p)‖ := by
  have he :
    D * (gaussianGammaMellinKernel.function ((c : ℂ) + Complex.I * t) * p) =
      (D * (gammaMellinKernel.function ((c : ℂ) + Complex.I * t) * p)) *
        Complex.exp ((((c : ℂ) + Complex.I * t) ^ 2) / 4) := by
    change
      D *
          ((Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2) *
              Complex.exp ((((c : ℂ) + Complex.I * t) ^ 2) / 4)) *
            p) =
        (D * (Complex.Gamma ((c : ℂ) + Complex.I * t + 1 / 2) * p)) *
          Complex.exp ((((c : ℂ) + Complex.I * t) ^ 2) / 4)
    ring
  rw [he, norm_mul]
  exact
    (mul_le_mul_of_nonneg_left (Analysis.norm_gaussian_multiplier_vertical_le c t)
          (norm_nonneg _)).trans_eq
      (mul_comm _ _)

/-- The Gaussian multiplier on the fixed left line -9/16 is at most 11/10.
A four-term exponential upper bound certifies this rational allowance. -/
theorem gaussian_left_multiplier_le : Real.exp ((-9 / 16 : ℝ) ^ 2 / 4) ≤ 11 / 10 := by
  have h :=
    Real.exp_bound' (x := ((-9 / 16 : ℝ) ^ 2 / 4)) (n := 4) (by norm_num only) (by norm_num only)
      (by decide)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_ofNat] at h
  linarith only [h]

/-- For every character and positive scale, the actual central Gaussian
archimedean integrand is at most 30/(1+t²). Its multiplier has norm at most one,
so the proved Gamma pointwise envelope applies before integration. -/
theorem gaussian_archimedean_integrand_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (t : ℝ) :
    ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      30 * (1 + t ^ 2)⁻¹ := by
  have h :=
    gaussian_kernel_integrand_norm_le 0 t (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2))
      ((x : ℂ) ^ (Complex.I * t))
  simp only [Complex.ofReal_zero, zero_add, zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero,
    one_mul] at h
  exact h.trans (gamma_archimedean_integrand_bound χ hx t)

/-- For every character and positive scale, the normalized central Gaussian
archimedean integral has norm at most fifteen. Integrate the majorant
30/(1+t²), whose integral is 30π, then divide by 2π.
The bound is independent of modulus, parity and scale. -/
theorem norm_gaussian_central_integral_le_fifteen {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
      15 := by
  let F := fun t : ℝ ↦
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
      (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  have hfi : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_gammaFactor_power_line gaussianGammaMellinKernel χ (c := 0)
        (by norm_num only) (by linarith only [gaussianGammaMellinKernel.delta_pos])
        (by norm_num only) hx
    simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using hi
  have hgi := integrable_inv_one_add_sq.const_mul (30 : ℝ)
  have hbound :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gaussian_archimedean_integrand_bound χ hx t))
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
Gaussian archimedean integral has norm at most fifteen. Move the integral to the
central line using the proved contour identity and apply its explicit bound.
This supplies a numerical archimedean constant to the fixed-kernel formula. -/
theorem norm_gaussian_right_integral_le_fifteen {q : ℕ} (χ : DirichletCharacter ℂ q) {b x : ℝ}
    (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + gaussianGammaMellinKernel.delta) (hb2 : b ≤ 3 / 2)
    (hx : 1 ≤ x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((b : ℂ) + Complex.I * t + 1 / 2) *
              (gaussianGammaMellinKernel.function ((b : ℂ) + Complex.I * t) *
                (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      15 := by
  rw [MellinKernel.gammaIntegral_eq_central gaussianGammaMellinKernel χ hb hbK hb2 hx]
  exact norm_gaussian_central_integral_le_fifteen χ (zero_lt_one.trans_le hx)

/-- Under GRH and primitive nonprincipal data, the Gaussian arithmetic sum
differs from its completed residue, zero sum and left integral by at most fifteen,
for admissible contour lines and scale x≥1. Substitute the exact completed
formula and apply the explicit right archimedean bound.
The left integral and kernel-pole residue remain explicit for subsequent estimates. -/
theorem norm_gaussian_completed_remainder_le_fifteen {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - gaussianGammaMellinKernel.delta < a)
    (hb : b ≤ 1 / 2 + gaussianGammaMellinKernel.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (hal : a < -1 / 2) (hbr : 1 / 2 < b) :
    ‖(∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) -
          (MellinKernel.weightedResidue gaussianGammaMellinKernel
                (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
              (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                  (gaussianGammaMellinKernel.function ((a : ℂ) + Complex.I * t) *
                    (x : ℂ) ^ ((a : ℂ) + Complex.I * t))))‖ ≤
      15 := by
  have h :=
    MellinKernel.tsum_summand_eq_completed_residue_formula gaussianGammaMellinKernel hq hGRH hp hne
      hinv hab ha hb ha' hb' hx hal hbr
  dsimp only at h
  rw [h, add_sub_cancel_left]
  exact norm_gaussian_right_integral_le_fifteen χ (by linarith only [hbr]) hb hb' hx

/-- For every character and positive scale, the actual central Gaussian
archimedean integrand is at most 30exp(-7|t|/5). Compare the actual integrands
using the multiplier bound one. This supplies the sharper integral constant 64/9. -/
theorem gaussian_archimedean_integrand_exp_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (t : ℝ) :
    ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      30 * Real.exp (-(7 / 5) * |t|) := by
  have h :=
    gaussian_kernel_integrand_norm_le 0 t (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2))
      ((x : ℂ) ^ (Complex.I * t))
  simp only [Complex.ofReal_zero, zero_add, zero_pow (by decide : 2 ≠ 0), zero_div, Real.exp_zero,
    one_mul] at h
  exact h.trans (gamma_archimedean_integrand_exp_bound χ hx t)

/-- For every character and positive scale, the normalized central Gaussian integral
has norm at most 64/9. Integrate the exponential envelope and use π>3.14.
The bound is uniform in modulus, parity and scale. -/
theorem norm_gaussian_central_integral_le_sixty_four_ninths {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
      64 / 9 := by
  let F := fun t : ℝ ↦
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
      (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  have hfi : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_gammaFactor_power_line gaussianGammaMellinKernel χ (c := 0)
        (by norm_num only) (by linarith only [gaussianGammaMellinKernel.delta_pos])
        (by norm_num only) hx
    simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using hi
  have hgi :=
    (Analysis.integrable_exp_neg_mul_abs (by norm_num only : (0 : ℝ) < 7 / 5)).const_mul (30 : ℝ)
  have hbound :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gaussian_archimedean_integrand_exp_bound χ hx t))
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
theorem norm_gaussian_right_integral_le_sixty_four_ninths {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + gaussianGammaMellinKernel.delta) (hb2 : b ≤ 3 / 2)
    (hx : 1 ≤ x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((b : ℂ) + Complex.I * t + 1 / 2) *
              (gaussianGammaMellinKernel.function ((b : ℂ) + Complex.I * t) *
                (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      64 / 9 := by
  rw [MellinKernel.gammaIntegral_eq_central gaussianGammaMellinKernel χ hb hbK hb2 hx]
  exact norm_gaussian_central_integral_le_sixty_four_ninths χ (zero_lt_one.trans_le hx)

/-- Under GRH and primitive nonprincipal data, the completed Gaussian arithmetic
formula has archimedean remainder at most 64/9 on admissible contour lines.
Substitute the exact formula and apply the right-line integral bound.
The residue, zero sum and left integral remain explicit for later estimates. -/
theorem norm_gaussian_completed_remainder_le_sixty_four_ninths {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - gaussianGammaMellinKernel.delta < a)
    (hb : b ≤ 1 / 2 + gaussianGammaMellinKernel.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (hal : a < -1 / 2) (hbr : 1 / 2 < b) :
    ‖(∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) -
          (MellinKernel.weightedResidue gaussianGammaMellinKernel
                (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
              (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                  (gaussianGammaMellinKernel.function ((a : ℂ) + Complex.I * t) *
                    (x : ℂ) ^ ((a : ℂ) + Complex.I * t))))‖ ≤
      64 / 9 := by
  have h :=
    MellinKernel.tsum_summand_eq_completed_residue_formula gaussianGammaMellinKernel hq hGRH hp hne
      hinv hab ha hb ha' hb' hx hal hbr
  dsimp only at h
  rw [h, add_sub_cancel_left]
  exact norm_gaussian_right_integral_le_sixty_four_ninths χ (by linarith only [hbr]) hb hb' hx

end PseudoPrime.LLS.PaperStatements
