/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaReflectedEulerIntegral
public import PseudoPrime.LLS.TwoPoleConstantBounds

/-! # Separate archimedean and inverted Euler costs in the Gamma remainder -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For nonprincipal positive-level data, completed minus ordinary logarithmic
derivatives on the reflected line have norm at most 11+abs t. Identify the difference
with the gamma-factor derivative and use its certified bound. This removes the
ordinary Euler cost from the archimedean envelope. -/
theorem norm_reflected_archimedean_difference_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) -
          logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))‖ ≤
      11 + |t| := by
  let s : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
  have hr : s.re = 17 / 16 := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = -t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, zero_add]
  have hr1 : 1 ≤ s.re := by
    rw [hr]; norm_num only
  have hp : 0 < s.re := zero_lt_one.trans_le hr1
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr1) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have hg := norm_logDeriv_gammaFactor_seventeen_sixteenths_le χ hr
  rw [hi, abs_neg] at hg
  change ‖logDeriv χ.completedLFunction s - logDeriv χ.LFunction s‖ ≤ _
  rw [he]
  calc
    _ = ‖logDeriv χ.gammaFactor s‖ := congrArg norm (by ring)
    _ ≤ _ := hg

/-- For nonprincipal data and positive scale, the actual archimedean integrand is
bounded by x^(-9/16) times eleven zeroth envelopes plus the first envelope.
Use the gamma-factor bound before multiplying the certified Gamma moments.
This supplies the pointwise majorant for the separated integral. -/
theorem gammaReflectedArchimedeanIntegrand_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖(logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) -
            logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))) *
          gammaSignedLeftWeight x t‖ ≤
      x ^ (-9 / 16 : ℝ) *
        (11 * PseudoPrime.Analysis.gammaRefinedZeroEnvelope t +
          PseudoPrime.Analysis.gammaRefinedFirstEnvelope t) := by
  have hd := norm_reflected_archimedean_difference_le hne t
  let z : ℂ := ((-1 / 16 : ℝ) : ℂ) + t * Complex.I
  have hz : z.re = -1 / 16 := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : z.im = t := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add, add_zero]
  have h0 := PseudoPrime.Analysis.norm_Gamma_le_gammaRefinedZeroEnvelope hz
  have h1 := PseudoPrime.Analysis.norm_Gamma_mul_height_le_gammaRefinedFirstEnvelope hz
  rw [hi] at h0 h1
  change ‖Complex.Gamma z‖ ≤ PseudoPrime.Analysis.gammaRefinedZeroEnvelope t at h0
  change ‖Complex.Gamma z‖ * |t| ≤ PseudoPrime.Analysis.gammaRefinedFirstEnvelope t at h1
  have hdg := mul_le_mul_of_nonneg_right hd (norm_nonneg (Complex.Gamma z))
  have he := add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num only : (0 : ℝ) ≤ 11)) h1
  have hb :
    ‖logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) -
            logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))‖ *
        ‖Complex.Gamma z‖ ≤
      11 * PseudoPrime.Analysis.gammaRefinedZeroEnvelope t +
        PseudoPrime.Analysis.gammaRefinedFirstEnvelope t := by
    nlinarith only [hdg, he]
  dsimp only [gammaSignedLeftWeight]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hr : ((((-9 / 16 : ℝ) : ℂ) + t * Complex.I)).re = -9 / 16 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [hr, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx.le _)).trans_eq (mul_comm _ _)

/-- For primitive nonprincipal data with nonprincipal inverse and positive scale,
the inverse character's actual archimedean integral norm is at most (35/2)x^(-9/16).
Separate ordinary and completed integrable functions, then integrate the certified
zeroth and first Gamma moments. This provides an explicit completed remainder cost. -/
theorem norm_gammaReflectedArchimedeanIntegral_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖gammaReflectedArchimedeanIntegral χ⁻¹ x‖ ≤ (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let F := fun t : ℝ ↦
    (logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) -
        logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))) *
      gammaSignedLeftWeight x t
  have hr := integrable_gammaSignedLeftRemainder hp hne hinv hx
  have he (t : ℝ) :
    gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t =
      logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
        gammaSignedLeftWeight x t := by
    rw [gammaSignedLeftIntegrand_reflection hp hne hinv, add_mul, add_sub_cancel_left]
  have hc := hr.congr (MeasureTheory.ae_of_all _ he)
  have hi := integrable_gamma_reflected_ordinary_logDeriv χ⁻¹ hx
  have hfi : MeasureTheory.Integrable F := by simpa only [F, Pi.sub_def, sub_mul] using hc.sub hi
  let E := fun t : ℝ ↦
    x ^ (-9 / 16 : ℝ) *
      (11 * Analysis.gammaRefinedZeroEnvelope t + Analysis.gammaRefinedFirstEnvelope t)
  have hEi : MeasureTheory.Integrable E :=
    ((Analysis.gammaRefinedZeroEnvelope_integrable.const_mul 11).add
          Analysis.gammaRefinedFirstEnvelope_integrable).const_mul
      _
  have hb :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hEi
        (fun t ↦ gammaReflectedArchimedeanIntegrand_bound hinv hx t))
  have hm := gamma_sharp_left_envelope_normalized_le (C := 11) (by norm_num only)
  norm_num only at hm
  have hpi : 0 ≤ (1 / (2 * Real.pi) : ℝ) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le)
  have hmul := mul_le_mul_of_nonneg_left hb hpi
  dsimp only [E] at hmul
  rw [MeasureTheory.integral_const_mul] at hmul
  have hm' := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hx.le (-9 / 16))
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi]
  nlinarith only [hmul, hm']

/-- For primitive nonprincipal data under GRH with ambient level at least 20000
and scale at least two, the actual summand-plus-zero remainder has the pole cost,
signed conductor cost and separated left error (35/2)x^(-9/16)+1/(x sqrt x).
Insert the explicit archimedean bound into the exact Euler split. This improves
the previous uniform left cost without a new analytic assumption. -/
theorem re_gamma_primitive_remainder_le_reflected_split {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x) :
    ((∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm (Real.log m) x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  have hr := re_gamma_primitive_remainder_le_archimedean_add_euler hq hm hmq hp hne hinv hGRH hx
  have ha := norm_gammaReflectedArchimedeanIntegral_le hp hne hinv (by linarith only [hx] : 0 < x)
  linarith only [hr, ha]

/-- For primitive nonprincipal data under GRH and a scalar two-pole Gamma cap,
retain both finite Euler savings while using the separated left error.
Combine the zero-sum norm with the actual improved completed remainder.
This is the arithmetic upper-bound interface for the witness comparisons. -/
theorem gamma_primitive_sum_re_le_twoPole_reflected_split {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {C : ℝ}
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ ≤ C) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log m / 2 + C -
          (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) *
            (∑ n ∈ B,
              Real.log n *
                AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm (Real.log m) x +
        (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        1 / (x * Real.sqrt x) := by
  have hz :=
    norm_gamma_oscillatingZeroSum_le_twoPole_constant (by linarith only [hm] : 2 ≤ m) hGRH hp hne
      hinv (by linarith only [hx] : 0 < x) hC A B
  have hr := re_gamma_primitive_remainder_le_reflected_split hq hm hmq hp hne hinv hGRH hx
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz, hr, hn]

/-- At every scale at least one, the separated left error is strictly less than
43x^(-9/16). Bound x^(-3/2) by x^(-9/16) using exponent monotonicity.
This certifies a uniform improvement over the old left-contour allowance. -/
theorem reflected_split_left_error_lt_old {x : ℝ} (hx : 1 ≤ x) :
    (35 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) + 1 / (x * Real.sqrt x) < 43 * x ^ (-9 / 16 : ℝ) := by
  have hx0 := zero_lt_one.trans_le hx
  have he : 1 / (x * Real.sqrt x) = x ^ (-3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = -(1 + 1 / 2) by ring, Real.rpow_neg hx0.le, Real.rpow_add hx0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
    exact one_div _
  have hb := Real.rpow_le_rpow_of_exponent_le hx (by norm_num only : (-3 / 2 : ℝ) ≤ -9 / 16)
  have hp := Real.rpow_pos_of_pos hx0 (-9 / 16 : ℝ)
  rw [he]
  linarith only [hb, hp]

end PseudoPrime.LLS.PaperStatements
