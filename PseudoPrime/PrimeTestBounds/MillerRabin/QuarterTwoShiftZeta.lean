/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftReflected
public import PseudoPrime.Analysis.CauchyWeightedIntegrals
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZeroExclusion
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftPairZeros
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors
public import PseudoPrime.LLS.PaperStatements.MellinKernelPrincipalBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMellin
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2

/-! # The principal forward sum in the two-frequency contour comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right-line xi logarithmic derivative and the two simple pole integrals
for the sixth-pole test at scale x. The even Gamma term is accounted for separately. -/
noncomputable def twoShiftXiPoles (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let W := fun t : ℝ ↦ quarterKernel570.function (s t) * (x : ℂ) ^ (s t)
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ((∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t) +
      (∫ t : ℝ, (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W t) +
      (∫ t : ℝ, (1 / (s t - ((1 / 2 : ℝ) : ℂ))) * W t))

/-- On the right line of real part 9/16 the level-one forward sum splits into
the xi logarithmic derivative, the two simple poles, and the principal gamma
integral for every admissible kernel with strip width 1/8. -/
private theorem twoShift_level_one_forward (K : LLS.PaperStatements.MellinKernel)
    (hd : K.delta = 1 / 8) {x : ℝ} (hx : 0 < x) :
    let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t : ℝ ↦ K.function (s t) * (x : ℂ) ^ s t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) =
      d *
          ((∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t) +
            (∫ t : ℝ, (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W t) +
            ∫ t : ℝ, (1 / (s t - ((1 / 2 : ℝ) : ℂ))) * W t) +
        d * ∫ t : ℝ, logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (s t + 1 / 2) * W t := by
  have hbright : (1 / 2 : ℝ) < 9 / 16 := by norm_num only
  have hb : (9 / 16 : ℝ) ≤ 1 / 2 + K.delta := by
    rw [hd]; norm_num only
  have hb' : (9 / 16 : ℝ) ≤ 1 := by norm_num only
  have hbl : -1 / 2 - K.delta < (9 / 16 : ℝ) := by
    rw [hd]; norm_num only
  have hbn : (9 / 16 : ℝ) ≠ -1 / 2 := by norm_num only
  let s := fun t : ℝ => ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let W := fun t : ℝ => K.function (s t) * (x : ℂ) ^ (s t)
  let F := fun t : ℝ => -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t
  let P := fun t : ℝ => (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W t
  let Q := fun t : ℝ => (1 / (s t - ((1 / 2 : ℝ) : ℂ))) * W t
  let G := fun t : ℝ => logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (s t + 1 / 2) * W t
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hiF : MeasureTheory.Integrable F :=
    LLS.PaperStatements.MellinKernel.integrable_xi_right_line K hbright hb hb' hx
  have hiP : MeasureTheory.Integrable P := by
    simpa only [P, W, s, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hbl hb hbn hbn hx
  have hiQ : MeasureTheory.Integrable Q := by
    simpa only [Q, W, s, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hbl hb hbn hbright.ne' hx
  have hiG : MeasureTheory.Integrable G := by
    simpa only [G, W, s, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K
        (1 : DirichletCharacter ℂ 1) (by linarith only [hbright]) hb (by linarith only [hb']) hx
  have he (t : ℝ) : -logDeriv riemannZeta (s t + 1 / 2) * W t = F t + P t + Q t + G t := by
    have hr : 1 < (s t + 1 / 2).re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
        Complex.one_re]
      linarith only [hbright]
    dsimp only [F, P, Q, G]
    rw [AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hr]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hf :
    (fun t : ℝ => -logDeriv riemannZeta (s t + 1 / 2) * W t) = (fun t => F t + P t + Q t + G t) :=
    funext he
  have hsum := LLS.PaperStatements.MellinKernel.levelOne_summand_integral_zeta K hx hbright hb
  change
    (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n) =
      d * (∫ t : ℝ, -logDeriv riemannZeta (s t + 1 / 2) * W t) at hsum
  have hfp := MeasureTheory.integral_add hiF hiP
  have hfpq := MeasureTheory.integral_add (hiF.add hiP) hiQ
  have hfpqg := MeasureTheory.integral_add ((hiF.add hiP).add hiQ) hiG
  simp only [Pi.add_def] at hfp hfpq hfpqg
  rw [hf, hfpqg, hfpq, hfp] at hsum
  change _ = d * ((∫ t : ℝ, F t) + (∫ t : ℝ, P t) + ∫ t : ℝ, Q t) + d * ∫ t : ℝ, G t
  rw [hsum]
  ring

/-- At every positive scale the level-one forward sum is the sum of the xi and
two pole integrals and the right Gamma integral. All integrals are on Re(s)=9/16. -/
theorem twoShift_zeta_forward {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) x n) =
      twoShiftXiPoles x + rightGamma570 (1 : DirichletCharacter ℂ 1) x := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  exact twoShift_level_one_forward quarterKernel570 hd hx

/-- For an even character the right Gamma term cancels exactly against the
one in the principal forward sum. Only the conductor, left archimedean term,
reflected integral, xi integral and poles remain. -/
theorem twoShift_even_zeta_cancel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    contourNonEuler570 χ x - reflectedIntegral570 χ x -
        (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ : ℂ)).re +
          (reflectedArch570 χ⁻¹ x).re -
        reflectedIntegral570 χ x -
        (twoShiftXiPoles x).re := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  rw [twoShift_zeta_forward hx, Complex.add_re]
  unfold contourNonEuler570 rightGamma570
  rw [hg]
  ring

/-- For a primitive even character trivial on primes through X, subtracting
the two shifted zero sums cancels the right Gamma contribution at both scales. -/
theorem twoShift_even_zero_difference {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprim : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ ≠ 1) (he : χ.Even) {X : ℝ} (hx : 0 < X) (hcut : 1 ≤ X * Real.exp (-3))
    (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let Z := fun y : ℝ ↦ (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ y ρ).re
    let R := fun y : ℝ ↦
      (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹ : ℂ)).re +
          (reflectedArch570 χ⁻¹ y).re -
        reflectedIntegral570 χ y -
        (twoShiftXiPoles y).re
    Z (X * Real.exp (-(14 / 5))) - Z (X * Real.exp (-3)) =
      R (X * Real.exp (-(14 / 5))) - R (X * Real.exp (-3)) := by
  intro Z R
  exact
    (twoShift_zero_difference hq hG hprim hn hi hx hcut hp).trans
      (congrArg₂ (· - ·) (twoShift_even_zeta_cancel χ he (mul_pos hx (Real.exp_pos _)))
        (twoShift_even_zeta_cancel χ he (mul_pos hx (Real.exp_pos _))))

/-- The positive zeta pole contributes the explicit main term at scale x.
Moving its remaining integral to the imaginary axis leaves the xi and negative
pole terms on the right line. This identity applies at both shifted scales. -/
theorem twoShift_xi_poles_sub_main {x : ℝ} (hx : 1 ≤ x) :
    let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun z : ℂ ↦ quarterKernel570.function z * (x : ℂ) ^ z
    let p := ((1 / 2 : ℝ) : ℂ)
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    twoShiftXiPoles x - W p =
      d *
        ((∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W (s t)) +
          (∫ t : ℝ, (1 / (s t - ((-1 / 2 : ℝ) : ℂ))) * W (s t)) +
          (∫ t : ℝ, (1 / (Complex.I * t - p)) * W (Complex.I * t))) := by
  intro s W p d
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.poleIntegral_sub_residue_central quarterKernel570 (p := 1 / 2)
      (b := 9 / 16) (by norm_num only) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      hx
  unfold twoShiftXiPoles
  dsimp only [s, W, p, d]
  linear_combination h

/-- At either half-unit pole the normalized central integral has norm at most
3/8 for every positive scale. The pole factor has norm at most two and the
sixth-order kernel has normalized mass 3/16. -/
theorem twoShift_central_pole_bound {p x : ℝ} (hpabs : |p| = 1 / 2) (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            (1 / (Complex.I * t - (p : ℂ))) *
              (quarterKernel570.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
      3 / 8 := by
  let K := quarterKernel570
  have hp : p ≠ 0 := abs_pos.mp (hpabs.trans_gt (by norm_num only))
  have hc : -1 / 2 - K.delta < (0 : ℝ) := by linarith only [K.delta_pos]
  have hc' : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
  have hn : (0 : ℝ) ≠ -1 / 2 := by norm_num only
  have hiK := LLS.PaperStatements.MellinKernel.integrable_line_in_strip K hc hc' hn
  let D := (1 / |p|) * (∫ t : ℝ, ‖K.function (Complex.I * t)‖)
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let F := fun t : ℝ =>
    (1 / (Complex.I * t - (p : ℂ))) * (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  have hiF : MeasureTheory.Integrable F := by
    simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hc hc' hn (Ne.symm hp) hx
  have hb (t : ℝ) : ‖F t‖ ≤ (1 / |p|) * ‖K.function (Complex.I * t)‖ := by
    have hden := Complex.abs_re_le_norm (Complex.I * t - (p : ℂ))
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub, abs_neg] at hden
    have hi := one_div_le_one_div_of_le (abs_pos.mpr hp) hden
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
    rw [one_div, norm_inv, ← one_div]
    exact mul_le_mul_of_nonneg_right hi (norm_nonneg _)
  have hiH : MeasureTheory.Integrable (fun t : ℝ => (1 / |p|) * ‖K.function (Complex.I * t)‖) := by
    simpa only [Complex.ofReal_zero, zero_add] using hiK.norm.const_mul (1 / |p|)
  have hi :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hiF.norm hiH hb)
  rw [MeasureTheory.integral_const_mul] at hi
  change ‖∫ t : ℝ, F t‖ ≤ D at hi
  change ‖d * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul]
  have hm : K.mass = 3 / 16 :=
    LLS.PaperStatements.rationalPole_six_mass (by norm_num only) (by norm_num only)
  change (∫ t : ℝ, ‖K.function (Complex.I * t)‖) / (2 * Real.pi) = 3 / 16 at hm
  apply (mul_le_mul_of_nonneg_left hi (norm_nonneg d)).trans_eq
  dsimp only [d, D]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hpabs]
  calc
    _ = 2 * ((∫ t : ℝ, ‖K.function (Complex.I * t)‖) / (2 * Real.pi)) := by ring
    _ = _ := by
      rw [hm]; norm_num only

/-- At scales at least one, the two zeta poles contribute their explicit
main term with error at most 3/4 after the xi integral is removed.
Move both errors to the central line and add their half-unit pole bounds. -/
theorem twoShift_xi_pole_error {x : ℝ} (hx : 1 ≤ x) :
    let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun z : ℂ ↦ quarterKernel570.function z * (x : ℂ) ^ z
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    ‖twoShiftXiPoles x - W ((1 / 2 : ℝ) : ℂ) -
          d *
            (∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W (s t))‖ ≤
      3 / 4 := by
  intro s W d
  let C := fun p : ℝ ↦ ∫ t : ℝ, (1 / (Complex.I * t - (p : ℂ))) * W (Complex.I * t)
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hn :=
    LLS.PaperStatements.MellinKernel.poleIntegral_eq_central_of_neg quarterKernel570 (p := -1 / 2)
      (b := 9 / 16) (by norm_num only) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      hx
  have he := twoShift_xi_poles_sub_main hx
  dsimp only at he
  rw [hn] at he
  have hbound (p : ℝ) (hp : |p| = 1 / 2) : ‖d * C p‖ ≤ 3 / 8 :=
    twoShift_central_pole_bound hp (zero_lt_one.trans_le hx)
  have hsum :=
    (norm_add_le (d * C (-1 / 2)) (d * C (1 / 2))).trans
      (add_le_add (hbound _ (by norm_num only [abs_neg, abs_div, abs_one]))
        (hbound _ (by norm_num only [abs_div, abs_one])))
  dsimp only [W, s, d]
  rw [he]
  rw [mul_add, mul_add, add_assoc, add_sub_cancel_left]
  exact hsum.trans_eq (by norm_num only)

/-- At positive scales the Mellin phase difference is bounded by the absolute
logarithmic separation times the height. Factor out the unit phase at y and
apply the chord bound on the unit circle. -/
theorem twoShift_phase_gap {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    ‖(x : ℂ) ^ (Complex.I * t) - (y : ℂ) ^ (Complex.I * t)‖ ≤ |Real.log x - Real.log y| * |t| := by
  let z := (y : ℂ) ^ (Complex.I * t)
  have hz : ‖z‖ = 1 := by
    rw [show z = (y : ℂ) ^ (Complex.I * t) from rfl, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, Real.rpow_zero]
  have he :
    (x : ℂ) ^ (Complex.I * t) =
      z * Complex.exp (Complex.I * (((Real.log x - Real.log y) * t : ℝ) : ℂ)) := by
    dsimp only [z]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'), ← Complex.ofReal_log hx.le, ←
      Complex.ofReal_log hy.le, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub]
    congr 1
    ring
  rw [he, show (y : ℂ) ^ (Complex.I * t) = z from rfl, ← mul_sub_one, norm_mul, hz, one_mul]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (Real.log x - Real.log y) * t))

/-- The imaginary part of the pole denominator cancels the height in the
phase difference. The resulting bound holds uniformly at every real pole. -/
theorem twoShift_pole_phase_gap {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (p t : ℝ) :
    ‖((x : ℂ) ^ (Complex.I * t) - (y : ℂ) ^ (Complex.I * t)) / (Complex.I * t - (p : ℂ))‖ ≤
      |Real.log x - Real.log y| := by
  have hd := Complex.abs_im_le_norm (Complex.I * t - (p : ℂ))
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add, sub_zero] at hd
  rw [norm_div]
  by_cases h : ‖Complex.I * t - (p : ℂ)‖ = 0
  · rw [h, div_zero]
    exact abs_nonneg _
  exact
    (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))).mpr
      ((twoShift_phase_gap hx hy t).trans (mul_le_mul_of_nonneg_left hd (abs_nonneg _)))

/-- For the shifts 14/5 and 3 the normalized integral of the differenced
pole phases costs at most 3/80 per pole. Integrate the uniform log-gap
bound 1/5 against the exact normalized sixth-order mass 3/16. -/
theorem twoShift_pole_integral_gap {X : ℝ} (hX : 0 < X) (p : ℝ) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let z := fun t : ℝ ↦ Complex.I * t
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            quarterKernel570.function (z t) * (((B : ℂ) ^ z t - (T : ℂ) ^ z t) / (z t - (p : ℂ)))‖ ≤
      3 / 80 := by
  intro B T z
  have hg : |Real.log B - Real.log T| = 1 / 5 := by
    dsimp only [B, T]
    rw [Real.log_mul hX.ne' (Real.exp_pos _).ne', Real.log_mul hX.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp, show Real.log X + -(14 / 5) - (Real.log X + -3) = 1 / 5 by ring,
      abs_of_pos (by norm_num only)]
  have hi :=
    LLS.PaperStatements.MellinKernel.integrable_line_in_strip quarterKernel570 (c := 0)
      (by linarith only [quarterKernel570.delta_pos])
      (by linarith only [quarterKernel570.delta_pos]) (by norm_num only)
  simp only [Complex.ofReal_zero, zero_add] at hi
  have hb :=
    MeasureTheory.norm_integral_le_of_norm_le (hi.norm.mul_const (1 / 5 : ℝ))
      (Filter.Eventually.of_forall
        (fun t : ℝ ↦
          (norm_mul _ _).le.trans
            (mul_le_mul_of_nonneg_left
              ((twoShift_pole_phase_gap (mul_pos hX (Real.exp_pos _)) (mul_pos hX (Real.exp_pos _))
                    p t).trans
                hg.le)
              (norm_nonneg (quarterKernel570.function (z t))))))
  rw [MeasureTheory.integral_mul_const] at hb
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq
  have hm : quarterKernel570.mass = 3 / 16 :=
    LLS.PaperStatements.rationalPole_six_mass (by norm_num only) (by norm_num only)
  change (∫ t : ℝ, ‖quarterKernel570.function (Complex.I * t)‖) / (2 * Real.pi) = 3 / 16 at hm
  calc
    _ = ((∫ t : ℝ, ‖quarterKernel570.function (Complex.I * t)‖) / (2 * Real.pi)) / 5 := by ring
    _ = _ := by
      rw [hm]; norm_num only

/-- The normalized central pole integral at scale x and real pole p. At each
nonzero pole its difference across the two shifted scales is absolutely convergent. -/
noncomputable def twoShiftCentralPole (p x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      (1 / (Complex.I * t - (p : ℂ))) *
        (quarterKernel570.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))

/-- Subtracting the actual integrals for a nonzero pole costs at most 3/80.
Absolute integrability at both scales permits subtraction inside the integral. -/
theorem twoShift_central_pole_diff {X p : ℝ} (hX : 0 < X) (hp : p ≠ 0) :
    ‖twoShiftCentralPole p (X * Real.exp (-(14 / 5))) - twoShiftCentralPole p (X * Real.exp (-3))‖ ≤
      3 / 80 := by
  let z := fun t : ℝ ↦ Complex.I * t
  let F := fun (x t : ℝ) ↦ (1 / (z t - (p : ℂ))) * (quarterKernel570.function (z t) * (x : ℂ) ^ z t)
  have hi {x : ℝ} (hx : 0 < x) : MeasureTheory.Integrable (F x) := by
    simpa only [F, z, Complex.ofReal_zero, zero_add, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel570 (c := 0)
        (by linarith only [quarterKernel570.delta_pos])
        (by linarith only [quarterKernel570.delta_pos]) (by norm_num only) hp.symm hx
  let B := X * Real.exp (-(14 / 5))
  let T := X * Real.exp (-3)
  have he (t : ℝ) :
    F B t - F T t =
      quarterKernel570.function (z t) * (((B : ℂ) ^ z t - (T : ℂ) ^ z t) / (z t - (p : ℂ))) := by
    dsimp only [F]
    simp only [div_eq_mul_inv]
    ring
  unfold twoShiftCentralPole
  rw [← mul_sub, ←
    MeasureTheory.integral_sub (hi (mul_pos hX (Real.exp_pos (-(14 / 5)))))
      (hi (mul_pos hX (Real.exp_pos (-3)))),
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact twoShift_pole_integral_gap hX p

/-- After the main term is removed, the sum of the two central pole errors
changes by at most 3/40 across the two scales. -/
theorem twoShift_both_poles_diff {X : ℝ} (hX : 0 < X) :
    let P := fun x ↦ twoShiftCentralPole (-1 / 2) x + twoShiftCentralPole (1 / 2) x
    ‖P (X * Real.exp (-(14 / 5))) - P (X * Real.exp (-3))‖ ≤ 3 / 40 := by
  intro P
  dsimp only [P]
  rw [add_sub_add_comm]
  exact
    (norm_add_le _ _).trans
      ((add_le_add (twoShift_central_pole_diff hX (by norm_num only : (-1 / 2 : ℝ) ≠ 0))
            (twoShift_central_pole_diff hX (by norm_num only : (1 / 2 : ℝ) ≠ 0))).trans_eq
        (by norm_num only))

/-- The normalized xi integral on the right contour at scale x. -/
noncomputable def twoShiftXiRight (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) *
        (quarterKernel570.function (s t) * (x : ℂ) ^ (s t))

/-- Subtracting the main term and right xi integral leaves exactly the two
central pole integrals at every scale at least one. -/
theorem twoShift_xi_error_exact {x : ℝ} (hx : 1 ≤ x) :
    twoShiftXiPoles x - quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) -
        twoShiftXiRight x =
      twoShiftCentralPole (-1 / 2) x + twoShiftCentralPole (1 / 2) x := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hn :=
    LLS.PaperStatements.MellinKernel.poleIntegral_eq_central_of_neg quarterKernel570 (p := -1 / 2)
      (b := 9 / 16) (by norm_num only) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      hx
  have he := twoShift_xi_poles_sub_main hx
  dsimp only at he
  rw [he, hn]
  unfold twoShiftXiRight twoShiftCentralPole
  ring

/-- At the shifted cutoffs with the smaller cutoff at least one, the change
in the actual xi-and-poles sum, after subtracting the changes of its main
term and xi integral, has norm at most 3/40. -/
theorem twoShift_xi_error_diff {X : ℝ} (hX : 0 < X) (hT : 1 ≤ X * Real.exp (-3)) :
    let E := fun x : ℝ ↦
      twoShiftXiPoles x -
        quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) -
        twoShiftXiRight x
    ‖E (X * Real.exp (-(14 / 5))) - E (X * Real.exp (-3))‖ ≤ 3 / 40 := by
  intro E
  have hB :=
    hT.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only : (-3 : ℝ) ≤ -(14 / 5)))
        hX.le)
  dsimp only [E]
  rw [twoShift_xi_error_exact hB, twoShift_xi_error_exact hT]
  exact twoShift_both_poles_diff hX

/-- The normalized xi integral on the left line at scale x. The power of x
has absolute value x^(-9/16) on this contour. -/
noncomputable def twoShiftXiLeft (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) *
        (quarterKernel570.function (s t) * (x : ℂ) ^ (s t))

/-- Under RH the normalized right xi integral at x at least one is the left
integral minus the oscillating zeta zero sum. The kernel residue vanishes. -/
theorem twoShift_xi_right_eq_left (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    twoShiftXiRight x = twoShiftXiLeft x - ∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have he :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity quarterKernel570 hRH (a := -9 / 16) (b :=
      9 / 16)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) hx
  simp only [pole_residue_zero_570, zero_sub, mul_comm _ Complex.I] at he
  rw [mul_assoc] at he
  have h := mul_left_cancel₀ Complex.I_ne_zero he
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u : ℂ ↦ d * u) h
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  unfold twoShiftXiRight twoShiftXiLeft
  rw [sub_eq_add_neg, add_comm]
  exact sub_eq_iff_eq_add.mp hh

/-- At both shifted cutoffs under RH the non-pole correction consists of the
left xi integral and the oscillating zero sum, with combined pole error 3/40. -/
theorem twoShift_zeta_zero_error (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hT : 1 ≤ X * Real.exp (-3)) :
    let E := fun x : ℝ ↦
      twoShiftXiPoles x -
        quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) -
        (twoShiftXiLeft x - ∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ)
    ‖E (X * Real.exp (-(14 / 5))) - E (X * Real.exp (-3))‖ ≤ 3 / 40 := by
  have hB :=
    hT.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only : (-3 : ℝ) ≤ -(14 / 5)))
        hX.le)
  have h := twoShift_xi_error_diff hX hT
  dsimp only at h ⊢
  rw [twoShift_xi_right_eq_left hRH hB, twoShift_xi_right_eq_left hRH hT] at h
  exact h

/-- Every xi zero lies above height six in absolute value under RH. There
the sixth-order kernel is bounded by one thousandth of the inverse-square
zero weight, including its multiplicity. -/
private theorem twoShift_zeta_term_small (hRH : RiemannHypothesis)
    (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖quarterKernel570.zetaKernelZeroTerm ρ‖ ≤
      (1 / 1000) *
        ((AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) /
          ‖(ρ : ℂ)‖ ^ 2) := by
  let t := (ρ : ℂ).im
  have hz :=
    AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH
      (AnalyticNumberTheory.RiemannXi.riemannZeta_zero_of_riemannXi_zero ρ.property)
      (AnalyticNumberTheory.RiemannXi.riemannXi_zero_re_nonneg ρ.property)
  have ht : 6 ≤ |t| := by linarith only [hz, Real.pi_gt_three]
  have ht2 : 36 ≤ t ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6) ht 2
    rw [sq_abs] at h
    linarith only [h]
  let D := 1 + (2 * (25 / 51 : ℝ) * t) ^ 2
  have hd : 35 ≤ D := by
    dsimp only [D]; nlinarith only [ht2]
  have hd2 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 35) hd 2
  have hn : ‖(ρ : ℂ)‖ ^ 2 = 1 / 4 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply,
      AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property]
    dsimp only [t]
    ring
  have hD : 0 < D := by linarith only [hd]
  have hscalar : (2 * (25 / 51 : ℝ)) / D ^ 3 ≤ (1 / 1000) / ‖(ρ : ℂ)‖ ^ 2 := by
    rw [hn, div_le_div_iff₀ (pow_pos hD _) (by positivity)]
    have h := mul_le_mul_of_nonneg_right hd2 hD.le
    dsimp only [D] at h ⊢
    nlinarith only [h, sq_nonneg t]
  rw [LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, norm_mul, Complex.norm_natCast]
  change _ * ‖Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5) (Complex.I * t)‖ ≤ _
  rw [Analysis.norm_rationalPoleFunction 3 (by norm_num only)]
  exact (mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg _)).trans_eq (by ring)

/-- The unmodulated absolute zeta mass for the sixth-order kernel is less
than the 1/12500 allowance in (96.17). Sum the height-sensitive term bound
and use the certified inverse-square mass under RH. -/
theorem twoShift_zeta_mass_small (hRH : RiemannHypothesis) :
    (∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖) < 1 / 12500 := by
  have hs :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel570 hRH).norm
  have h :=
    hs.tsum_le_tsum (twoShift_zeta_term_small hRH)
      ((AnalyticNumberTheory.RiemannXi.summable_inverse_square_mass_RH hRH).mul_left (1 / 1000))
  rw [tsum_mul_left, AnalyticNumberTheory.RiemannXi.tsum_zeroInvSq_eq_two_mass_RH hRH] at h
  linarith only [h, AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000]

/-- At any positive scale the oscillating zero sum is bounded by the
unmodulated mass, hence by the section 96 allowance under RH. -/
theorem twoShift_zeta_sum_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ‖ ≤ 1 / 12500 := by
  have h :=
    (LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterKernel570 hRH hx).norm
  apply (norm_tsum_le_tsum_norm h).trans
  rw [tsum_congr
      (LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm quarterKernel570 hx)]
  exact (twoShift_zeta_mass_small hRH).le

/-- The difference of the two oscillating xi sums at any positive scales
has norm at most 1/6250 under RH. -/
theorem twoShift_zeta_sum_diff_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ‖(∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ) -
          ∑' ρ, quarterKernel570.zetaOscillatingZeroTerm y ρ‖ ≤
      1 / 6250 := by
  exact
    (norm_sub_le _ _).trans
      ((add_le_add (twoShift_zeta_sum_bound hRH hx) (twoShift_zeta_sum_bound hRH hy)).trans_eq
        (by norm_num only))

/-- Under RH the sum of the pole and zero corrections in the two-scale
comparison has norm at most 1879/25000. Only the main term and the left
xi integral remain explicit. -/
theorem twoShift_zeta_left_error (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hT : 1 ≤ X * Real.exp (-3)) :
    let E := fun x : ℝ ↦
      twoShiftXiPoles x -
        quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ) -
        twoShiftXiLeft x
    ‖E (X * Real.exp (-(14 / 5))) - E (X * Real.exp (-3))‖ ≤ 1879 / 25000 := by
  intro E
  let Z := fun x : ℝ ↦ ∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ
  let B := X * Real.exp (-(14 / 5))
  let T := X * Real.exp (-3)
  have hz : ‖Z B - Z T‖ ≤ 1 / 6250 :=
    twoShift_zeta_sum_diff_bound hRH (mul_pos hX (Real.exp_pos _)) (mul_pos hX (Real.exp_pos _))
  have he := twoShift_zeta_zero_error hRH hX hT
  dsimp only at he
  have hh : ‖(E B - E T) + (Z B - Z T)‖ ≤ 3 / 40 := by
    convert he using 2
    dsimp only [E, Z, B, T]
    ring
  have h := norm_sub_le ((E B - E T) + (Z B - Z T)) (Z B - Z T)
  rw [add_sub_cancel_right] at h
  exact h.trans ((add_le_add hh hz).trans_eq (by norm_num only))

/-- The absolute xi integral on the left line at unit scale, normalized by
two pi. It is independent of both shifted cutoffs. -/
noncomputable def twoShiftXiLeftMass : ℝ :=
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  (1 / (2 * Real.pi)) *
    ∫ t : ℝ,
      ‖-logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) *
          quarterKernel570.function (s t)‖

/-- For positive x the left xi integral decays as x^(-9/16) times its
unit-scale absolute mass. The real part of the contour exponent is constant. -/
theorem twoShift_xi_left_decay {x : ℝ} (hx : 0 < x) :
    ‖twoShiftXiLeft x‖ ≤ twoShiftXiLeftMass * x ^ (-9 / 16 : ℝ) := by
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let A := fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2)
  let F := fun t : ℝ ↦ A t * (quarterKernel570.function (s t) * (x : ℂ) ^ s t)
  have he (t : ℝ) : ‖F t‖ = ‖A t * quarterKernel570.function (s t)‖ * x ^ (-9 / 16 : ℝ) := by
    dsimp only [F]
    rw [← mul_assoc, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi := MeasureTheory.norm_integral_le_integral_norm (μ := MeasureTheory.volume) F
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_mul_const] at hi
  unfold twoShiftXiLeft twoShiftXiLeftMass
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (by positivity)

/-- Removing the explicit main term from the two-scale xi-and-poles difference
costs at most the certified pole and zero errors plus the decaying left mass
at the two specified scales. -/
theorem twoShift_zeta_main_error (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hT : 1 ≤ X * Real.exp (-3)) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let E := fun x : ℝ ↦
      twoShiftXiPoles x - quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    ‖E B - E T‖ ≤ 1879 / 25000 + twoShiftXiLeftMass * (B ^ (-9 / 16 : ℝ) + T ^ (-9 / 16 : ℝ)) := by
  intro B T E
  have hb := twoShift_xi_left_decay (mul_pos hX (Real.exp_pos (-(14 / 5))))
  have ht := twoShift_xi_left_decay (mul_pos hX (Real.exp_pos (-3)))
  have hl := (norm_sub_le (twoShiftXiLeft B) (twoShiftXiLeft T)).trans (add_le_add hb ht)
  have he := twoShift_zeta_left_error hRH hX hT
  change ‖(E B - twoShiftXiLeft B) - (E T - twoShiftXiLeft T)‖ ≤ _ at he
  rw [sub_sub_sub_comm] at he
  have hh :=
    (norm_add_le ((E B - E T) - (twoShiftXiLeft B - twoShiftXiLeft T))
          (twoShiftXiLeft B - twoShiftXiLeft T)).trans
      (add_le_add he hl)
  rw [sub_add_cancel] at hh
  rw [mul_add]
  exact hh

/-- To the right of the critical line, RH bounds the xi logarithmic
derivative by a quadratic norm envelope with explicit coefficient 231/10000.
Use the genus-one expansion and sum its inverse-square mass. -/
theorem twoShift_xi_deriv_bound (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖logDeriv AnalyticNumberTheory.RiemannXi.riemannXi s‖ ≤
      (231 / 10000) * (1 + 2 * ‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2))) := by
  let D := ‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2))
  let G := fun ρ : ℂ ↦
    (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  have hsub : (∑' ρ : AnalyticNumberTheory.RiemannXi.Zero, G ρ) = ∑' ρ : ℂ, G ρ := by
    apply
      tsum_subtype_eq_of_support_subset (f := G) (s :=
        {ρ | AnalyticNumberTheory.RiemannXi.riemannXi ρ = 0})
    intro ρ hρ
    by_contra hn
    have ho : analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
    exact hρ (by simp only [G, ho, Nat.cast_zero, zero_mul])
  have hm := (AnalyticNumberTheory.RiemannXi.summable_inverse_square_mass_RH hRH).mul_left D
  have hb (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖G ρ‖ ≤
      D *
        ((AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) /
          ‖(ρ : ℂ)‖ ^ 2) := by
    dsimp only [G]
    rw [norm_mul, Complex.norm_natCast]
    have h :=
      AnalyticNumberTheory.General.norm_genusTerm_le_inverseSquare
        (AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH ρ.property) hs
    exact
      (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq
        (by
          unfold AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity D
          ring)
  have hz :=
    (norm_tsum_le_tsum_norm (hm.of_norm_bounded hb).norm).trans
      ((hm.of_norm_bounded hb).norm.tsum_le_tsum hb hm)
  rw [tsum_mul_left, AnalyticNumberTheory.RiemannXi.tsum_zeroInvSq_eq_two_mass_RH hRH, hsub] at hz
  have hc :
    ‖logDeriv AnalyticNumberTheory.RiemannXi.riemannXi 0‖ =
      AnalyticNumberTheory.RiemannXi.riemannZeroMass := by
    rw [AnalyticNumberTheory.RiemannXi.logDeriv_riemannXi_zero_eq]
    unfold AnalyticNumberTheory.RiemannXi.riemannZeroMass
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    congr 1
    push_cast
    rw [Complex.ofReal_log (by positivity)]
    push_cast
    rfl
  have he := AnalyticNumberTheory.RiemannXi.centered_logDeriv_eq_genusSum_RH hRH hs
  have ht :=
    (norm_add_le (∑' ρ : ℂ, G ρ) (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi 0)) |>.trans
      (add_le_add hz hc.le)
  rw [← eq_add_of_sub_eq he] at ht
  have hD : 0 ≤ D :=
    mul_nonneg (norm_nonneg _)
      (add_nonneg zero_le_one (div_nonneg (norm_nonneg _) (sub_pos.mpr hs).le))
  have hmass := AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
  change _ ≤ 231 / 10000 * (1 + 2 * ‖s‖ * (1 + ‖s‖ / (s.re - 1 / 2)))
  dsimp only [D] at ht hD
  nlinarith only [ht, hmass, mul_le_mul_of_nonneg_left hmass hD]

/-- On the left xi contour, reflection and the inverse-square mass give a
quadratic envelope in the height. The reflected real part is 17/16 and
its horizontal distance from the zero line is 9/16. -/
theorem twoShift_left_deriv_bound (hRH : RiemannHypothesis) (t : ℝ) :
    let s := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2
    let r := 17 / 16 + |t|
    ‖logDeriv AnalyticNumberTheory.RiemannXi.riemannXi s‖ ≤
      (231 / 10000) * (1 + 2 * r * (1 + r / (9 / 16))) := by
  intro s r
  let w := ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  have hr : w.re = 17 / 16 := by
    simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  have hw : 1 - w = s := by
    dsimp only [s, w]
    push_cast
    ring
  have hn : ‖w‖ ≤ r := by
    apply (norm_sub_le _ _).trans_eq
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num only : (0 : ℝ) ≤ 17 / 16), norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h :=
    twoShift_xi_deriv_bound hRH (s := w)
      (by
        rw [hr]; norm_num only)
  rw [hr, show (17 / 16 - 1 / 2 : ℝ) = 9 / 16 by norm_num only] at h
  rw [← hw, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub, norm_neg]
  exact h.trans (by gcongr)

/-- On the left line the denominator is a cubed Cauchy denominator of width 183/400. -/
private theorem quarter_left_norm (t : ℝ) :
    ‖quarterKernel570.function ((-9 / 16 : ℂ) + Complex.I * t)‖ =
      (51 / 50 : ℝ) ^ 5 * Real.exp (-(63 / 40)) / ((183 / 400 : ℝ) ^ 2 + t ^ 2) ^ 3 := by
  have hn :
    ‖((-9 / 16 : ℂ) + Complex.I * t) + ((2 * (25 / 51 : ℝ))⁻¹ : ℝ)‖ ^ 2 =
      (183 / 400 : ℝ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.div_re,
      Complex.div_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have he :
    ‖Complex.exp (2 * ((7 / 5 : ℝ) : ℂ) * ((-9 / 16 : ℂ) + Complex.I * t))‖ =
      Real.exp (-(63 / 40)) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.div_re,
      Complex.div_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  change ‖Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5) ((-9 / 16 : ℂ) + Complex.I * t)‖ = _
  rw [Analysis.rationalPole_eq_shifted_power 3 (by norm_num only) (7 / 5), norm_mul, norm_div,
    norm_pow, norm_div, norm_pow, he]
  simp only [pow_mul, hn]
  norm_num only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- Under RH the absolute left xi mass of the sixth-order kernel is at most
11. Dominate the integrand by four times the squared Cauchy density at the
actual pole distance and integrate that density exactly. -/
theorem twoShift_xi_mass_le (hRH : RiemannHypothesis) : twoShiftXiLeftMass ≤ 11 := by
  let d : ℝ := 183 / 400
  have hd : 0 < d := by norm_num only [d]
  have hb (t : ℝ) :
    ‖-logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
              (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      4 * (1 / (d ^ 2 + t ^ 2) ^ 2) := by
    have h := twoShift_left_deriv_bound hRH t
    dsimp only at h
    have h1 :
      (231 / 10000 : ℝ) * (1 + 2 * (17 / 16 + |t|) * (1 + (17 / 16 + |t|) / (9 / 16))) ≤
        2 * (d ^ 2 + t ^ 2) := by
      dsimp only [d]
      nlinarith only [sq_abs t, sq_nonneg (|t| - 1 / 4)]
    have he := Real.exp_le_one_iff.mpr (by norm_num only : -(63 / 40 : ℝ) ≤ 0)
    have h2 : (51 / 50 : ℝ) ^ 5 * Real.exp (-(63 / 40)) ≤ 2 := by linarith only [he]
    rw [norm_mul, norm_neg,
      show (((-9 / 16 : ℝ) : ℂ)) = (-9 / 16 : ℂ) by
        push_cast; rfl,
      quarter_left_norm]
    rw [show (((-9 / 16 : ℝ) : ℂ)) = (-9 / 16 : ℂ) by
        push_cast; rfl] at h
    apply
      (mul_le_mul (h.trans h1) (div_le_div_of_nonneg_right h2 (by positivity)) (by positivity)
          (by positivity)).trans_eq
    change 2 * (d ^ 2 + t ^ 2) * (2 / (d ^ 2 + t ^ 2) ^ 3) = _
    field_simp [show d ^ 2 + t ^ 2 ≠ 0 by positivity]
    ring
  have hi :=
    MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
      ((Analysis.integrable_scaled_cauchy_two hd).const_mul 4) (Filter.Eventually.of_forall hb)
  rw [MeasureTheory.integral_const_mul, Analysis.integral_scaled_cauchy_two hd] at hi
  unfold twoShiftXiLeftMass
  apply (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans
  dsimp only [d]
  field_simp [Real.pi_pos.ne']
  nlinarith only [Real.pi_pos, sq_pos_of_pos Real.pi_pos]

/-- Throughout the high cutoff range the difference of the two xi-and-poles
terms differs from the difference of their main terms by at most 13/25.
Both scales exceed 2500, so the left errors each cost at most 11/50. -/
theorem twoShift_high_zeta_error (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let E := fun x : ℝ ↦
      twoShiftXiPoles x - quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)
    ‖E B - E T‖ ≤ 13 / 25 := by
  intro B T E
  have hx : 0 < X := by linarith only [hX]
  have hex := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have ht : 2500 ≤ T := by
    dsimp only [T]
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),
      show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [hex, hX]
  have hb : 2500 ≤ B :=
    ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only)) hx.le)
  have hp {x : ℝ} (h : 2500 ≤ x) : x ^ (-9 / 16 : ℝ) ≤ 1 / 50 := by
    have h1 : 1 ≤ x := by linarith only [h]
    have hs : 50 ≤ Real.sqrt x :=
      (Real.le_sqrt (by norm_num only) (zero_le_one.trans h1)).mpr (by linarith only [h])
    apply (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num only : (-9 / 16 : ℝ) ≤ -(1 / 2))).trans
    rw [Real.rpow_neg (zero_le_one.trans h1), ← Real.sqrt_eq_rpow, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num only) hs
  have hh := twoShift_zeta_main_error hRH hx (show 1 ≤ T by linarith only [ht])
  change ‖E B - E T‖ ≤ _ at hh
  have hc :=
    mul_le_mul_of_nonneg_right (twoShift_xi_mass_le hRH)
      (add_nonneg (Real.rpow_nonneg (by linarith only [hb] : 0 ≤ B) (-9 / 16))
        (Real.rpow_nonneg (by linarith only [ht] : 0 ≤ T) (-9 / 16)))
  change
    ‖E B - E T‖ ≤ 1879 / 25000 + twoShiftXiLeftMass * (B ^ (-9 / 16 : ℝ) + T ^ (-9 / 16 : ℝ)) at hh
  linarith only [hh, hc, hp hb, hp ht]

/-- The main-term approximation to the even-character contour at one scale:
the conductor, reflected archimedean and reflected prime integrals minus the
principal pole main term. The high-range two-scale error is at most 13/25. -/
noncomputable def twoShiftEvenMain {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹ : ℂ)).re +
      (reflectedArch570 χ⁻¹ y).re -
    reflectedIntegral570 χ y -
    (quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (y : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re

/-- Under GRH a primitive even nonprincipal character trivial on primes up to
X has a two-scale zero difference within 13/25 of the explicit even contour
difference whenever X is at least 85264. -/
theorem twoShift_even_main_error {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprim : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ ≠ 1) (he : χ.Even) {X : ℝ} (hX : 85264 ≤ X)
    (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let Z := fun y : ℝ ↦ (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ y ρ).re
    |Z B - Z T - (twoShiftEvenMain χ B - twoShiftEvenMain χ T)| ≤ 13 / 25 := by
  intro B T Z
  have hx : 0 < X := by linarith only [hX]
  have hex := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have ht : 1 ≤ T := by
    dsimp only [T]
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul,
      show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [hex, hX]
  have h := twoShift_even_zero_difference hq hG hprim hn hi he hx ht hp
  have hz := twoShift_high_zeta_error hG.riemann hX
  dsimp only at h hz
  have hr := (Complex.abs_re_le_norm _).trans hz
  simp only [Complex.sub_re] at hr
  dsimp only [Z, B, T, twoShiftEvenMain]
  rw [h]
  apply le_trans (le_of_eq _) hr
  rw [← abs_neg]
  congr 1
  ring

/-- For a primitive even character trivial through the high cutoff, the
two-frequency phase lower bound loses at most 13/50 when replacing both
shifted zero sums by the conductor, reflected terms and principal main term. -/
theorem twoShift_even_phase_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprim : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ ≠ 1) (he : χ.Even) {X : ℝ} (hX : 85264 ≤ X)
    (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let W := fun s : ℝ ↦
      ∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (s * ρ.im)
    (W (14 / 5) - W 3 + twoShiftEvenMain χ (X * Real.exp (-(14 / 5))) -
            twoShiftEvenMain χ (X * Real.exp (-3))) /
          2 -
        (quarterMass570 χ - W (1 / 5)) / 4 -
        13 / 50 ≤
      twoShiftZeroPhase χ X := by
  intro W
  have ha := (abs_le.mp (twoShift_even_main_error hq hG hprim hn hi he hX hp)).1
  have hb :=
    quarter_zero_shifted_lower hq hG hprim hn hi (by linarith only [hX] : 0 < X) (14 / 5) 3 (1 / 2)
  dsimp only at ha hb
  rw [show (3 : ℝ) - 14 / 5 = 1 / 5 by norm_num only] at hb
  dsimp only [W, twoShiftZeroPhase]
  linarith only [ha, hb]

/-- The two-frequency lower approximation before the principal error is
deducted. Its cosine terms and shifted main terms are explicit for each
pair character of a uniform Korselt triple. -/
@[expose]
noncomputable def twoShiftPhaseApprox {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) : ℝ :=
  let W := fun s : ℝ ↦ ∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (s * ρ.im)
  (W (14 / 5) - W 3 + twoShiftEvenMain χ (X * Real.exp (-(14 / 5))) -
        twoShiftEvenMain χ (X * Real.exp (-3))) /
      2 -
    (quarterMass570 χ - W (1 / 5)) / 4

private theorem pair_phase_approx_lower {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hpk : p - 1 ∣ n - 1) (hqk : q - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    twoShiftPhaseApprox χ X - 13 / 50 ≤ twoShiftZeroPhase χ X := by
  intro χ
  have hpq : 2 ≤ p * q :=
    ((Fact.out : p.Prime).two_le).trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hne := pair_character_ne_one hsq hd (hp.mul hq) hpq
  exact
    twoShift_even_phase_lower hpq hG (pair_character_primitive hsq hd (hp.mul hq)) hne
      (inv_ne_one.mpr hne) (pair_character_even_of_korselt hn ho hp hq hpk hqk hv) hX
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right p q).trans hd)
          ((dvd_mul_left q p).trans hd) hd hpk hqk hv l (hpass l hl hlX))

/-- Under universal prime-base passage, the three Jacobi zero phases dominate the sum
of their explicit two-frequency approximations minus the combined error 39/50. -/
theorem twoShift_triple_phase_lower {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    twoShiftPhaseApprox a X + twoShiftPhaseApprox b X + twoShiftPhaseApprox c X - 39 / 50 ≤
      twoShiftZeroPhase a X + twoShiftZeroPhase b X + twoShiftZeroPhase c X := by
  intro a b c
  have ha := pair_phase_approx_lower hsq hn ho hp hq hpq hpk hqk hvq hG hX hpass
  have hb := pair_phase_approx_lower hsq hn ho hp hr hpr hpk hrk hvr hG hX hpass
  have hc := pair_phase_approx_lower hsq hn ho hq hr hqr hqk hrk (hvr.trans hvq.symm) hG hX hpass
  dsimp only at ha hb hc
  dsimp only [a, b, c]
  linarith only [ha, hb, hc]

/-- The high-cutoff prime-sum budget before adding the common zeta error.
The phase approximation subtracts the part of the zero mass recovered by
the two shifted explicit formulas. -/
@[expose]
noncomputable def twoShiftPrimeBudget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) : ℝ :=
  contourNonEuler570 χ X - reflectedIntegral570 χ X + quarterMass570 χ - twoShiftPhaseApprox χ X

private theorem pair_prime_budget_upper {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [Fact p.Prime]
    [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hpk : p - 1 ∣ n - 1) (hqk : q - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    (∑' n : ℕ, quarterKernel570.summand χ X n).re ≤ twoShiftPrimeBudget χ X + 13 / 50 := by
  intro χ
  have hpq : 2 ≤ p * q :=
    ((Fact.out : p.Prime).two_le).trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hne := pair_character_ne_one hsq hd (hp.mul hq) hpq
  have ha := pair_phase_approx_lower hsq hn ho hp hq hd hpk hqk hv hG hX hpass
  change twoShiftPhaseApprox χ X - 13 / 50 ≤ twoShiftZeroPhase χ X at ha
  unfold twoShiftZeroPhase at ha
  rw [zero_re_eq_contour_sub_prime hpq hG (pair_character_primitive hsq hd (hp.mul hq)) hne
      (inv_ne_one.mpr hne) (by linarith only [hX])] at ha
  unfold twoShiftPrimeBudget
  linarith only [ha]

/-- Universal prime-base passage bounds the sum of the three actual Jacobi prime sums
by their high-cutoff budgets plus the combined zeta error. -/
theorem twoShift_triple_prime_upper {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    (∑' n : ℕ, quarterKernel570.summand a X n).re + (∑' n : ℕ, quarterKernel570.summand b X n).re +
        (∑' n : ℕ, quarterKernel570.summand c X n).re ≤
      twoShiftPrimeBudget a X + twoShiftPrimeBudget b X + twoShiftPrimeBudget c X + 39 / 50 := by
  intro a b c
  have ha := pair_prime_budget_upper hsq hn ho hp hq hpq hpk hqk hvq hG hX hpass
  have hb := pair_prime_budget_upper hsq hn ho hp hr hpr hpk hrk hvr hG hX hpass
  have hc := pair_prime_budget_upper hsq hn ho hq hr hqr hqk hrk (hvr.trans hvq.symm) hG hX hpass
  dsimp only at ha hb hc
  dsimp only [a, b, c]
  linarith only [ha, hb, hc]

/-- A strict gap between the three-character contour budget and the principal
prefix including all eligible squares gives a rejecting prime base through X.
Universal passage would bound the same prime sum on both sides. -/
theorem twoShift_witness_of_gap {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hgap :
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
        let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
        let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
        let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
        let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
        let S := (Finset.Ioc 0 ⌊X⌋₊).filter (fun k : ℕ ↦ X < (k : ℝ) ^ 2)
        twoShiftPrimeBudget a X + twoShiftPrimeBudget b X + twoShiftPrimeBudget c X + 39 / 50 <
          4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) -
            (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_contra hnone
  have hpass (l : ℕ) (hl : l.Prime) (hx : (l : ℝ) ≤ X) :
    PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
    Classical.byContradiction (fun hf ↦ hnone ⟨l, hl, hx, hf⟩)
  have hu :=
    twoShift_triple_prime_upper hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hX hpass
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hx : 0 < X := by linarith only [hX]
  let S := (Finset.Ioc 0 ⌊X⌋₊).filter (fun k : ℕ ↦ X < (k : ℝ) ^ 2)
  have hs (k : ℕ) (hk : k ∈ S) : (k : ℝ) ≤ X ∧ X < (k : ℝ) ^ 2 :=
    ⟨(Nat.le_floor_iff hx.le).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).2,
      (Finset.mem_filter.mp hk).2⟩
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hl :=
    kernel_prefix_add_squares quarterKernel570 a b c hx S hs ht
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right p q).trans hpq)
          ((dvd_mul_left q p).trans hpq) hpq hpk hqk hvq l (hpass l hl hlX))
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hp hr ((dvd_mul_right p r).trans hpr)
          ((dvd_mul_left r p).trans hpr) hpr hpk hrk hvr l (hpass l hl hlX))
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hq hr ((dvd_mul_right q r).trans hqr)
          ((dvd_mul_left r q).trans hqr) hqr hqk hrk (hvr.trans hvq.symm) l (hpass l hl hlX))
  exact (not_lt_of_ge (hl.trans hu)) (hgap hpass)

/-- Subtracting the left xi integral from the reflected archimedean term
cancels the even gamma factor exactly. Only the two reflected pole integrals
and the ordinary zeta logarithmic derivative remain. -/
theorem twoShift_reflected_gamma_cancel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let W := fun t : ℝ ↦ quarterKernel570.function (s t) * (x : ℂ) ^ s t
    reflectedArch570 χ x - twoShiftXiLeft x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, -(1 / w t + 1 / (w t - 1) + logDeriv riemannZeta (w t)) * W t := by
  intro s w W
  let F := fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t
  let G := fun t : ℝ ↦ logDeriv χ.gammaFactor (w t) * W t
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hF : MeasureTheory.Integrable F :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line quarterKernel570
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have hw (t : ℝ) : w t = 1 / 2 - s t := by
    dsimp only [w, s]; push_cast; ring
  have hp (t : ℝ) : 1 < (w t).re := by
    simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    norm_num only
  let H := fun t : ℝ ↦ -(1 / w t + 1 / (w t - 1) + logDeriv riemannZeta (w t)) * W t
  have hid (t : ℝ) : G t - F t = H t := by
    have harg : s t + 1 / 2 = 1 - w t := by
      rw [hw]; ring
    dsimp only [G, F, H]
    rw [harg, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub,
      AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one (hp t), hg]
    ring
  have hP (p : ℝ) (hne : (-9 / 16 : ℝ) ≠ p) :
    MeasureTheory.Integrable (fun t : ℝ ↦ (1 / (s t - (p : ℂ))) * W t) := by
    simpa only [s, W, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel570
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) hne hx
  have hL := reflected_ordinary_integrable_570 (1 : DirichletCharacter ℂ 1) hx
  simp only [DirichletCharacter.LFunction_modOne_eq, Complex.ofReal_neg, mul_neg,
    ← sub_eq_add_neg] at hL
  have hH : MeasureTheory.Integrable H := by
    apply (((hP (1 / 2) (by norm_num only)).add (hP (-1 / 2) (by norm_num only))).add hL).congr
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [Pi.add_apply, H]
    rw [show w t = -(s t - ((1 / 2 : ℝ) : ℂ)) by
        rw [hw]; push_cast; ring,
      show -(s t - ((1 / 2 : ℝ) : ℂ)) - 1 = -(s t - ((-1 / 2 : ℝ) : ℂ)) by
        push_cast; ring]
    simp only [div_neg]
    dsimp only [w, s, W]
    push_cast
    ring_nf
  have hG : MeasureTheory.Integrable G :=
    (hH.add hF).congr (Filter.Eventually.of_forall (fun t ↦ (eq_add_of_sub_eq (hid t)).symm))
  rw [reflected_arch_eq_gamma_570 χ hn, twoShiftXiLeft, ← mul_sub, ←
    MeasureTheory.integral_sub hG hF]
  exact congrArg _ (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hid))

/-- The common reflected pole and ordinary zeta correction left after canceling
the gamma integrals, evaluated on the reflected line at scale x. -/
noncomputable def twoShiftReflectedZeta (x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      -(1 / w t + 1 / (w t - 1) + logDeriv riemannZeta (w t)) *
        (quarterKernel570.function (s t) * (x : ℂ) ^ s t)

/-- At the two positive shifted scales, the reflected gamma and xi-and-poles
difference is approximated by the reflected zeta correction minus the main
term with error at most 1879/25000, uniformly for nonprincipal even characters. -/
theorem twoShift_reflected_diff_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) (hRH : RiemannHypothesis) {X : ℝ} (hx : 0 < X) (hT : 1 ≤ X * Real.exp (-3)) :
    let E := fun x : ℝ ↦
      reflectedArch570 χ x - twoShiftXiPoles x -
        (twoShiftReflectedZeta x -
          quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ))
    ‖E (X * Real.exp (-(14 / 5))) - E (X * Real.exp (-3))‖ ≤ 1879 / 25000 := by
  intro E
  have hz {x : ℝ} (h : 0 < x) : reflectedArch570 χ x = twoShiftReflectedZeta x + twoShiftXiLeft x :=
    eq_add_of_sub_eq (twoShift_reflected_gamma_cancel χ hn he h)
  have h := twoShift_zeta_left_error hRH hx hT
  dsimp only at h
  dsimp only [E]
  rw [hz (mul_pos hx (Real.exp_pos _)), hz (mul_pos hx (Real.exp_pos _))]
  apply le_trans (le_of_eq _) h
  rw [← norm_neg]
  congr 1
  ring

/-- The normalized left-line integral for the pole p at scale x. Subtracting
this from its central-line counterpart isolates the residue between the lines. -/
noncomputable def twoShiftLeftPole (p x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, (1 / (s t - (p : ℂ))) * (quarterKernel570.function (s t) * (x : ℂ) ^ s t)

/-- At positive scale the reflected zeta correction is the sum of the two
left-line poles and the principal reflected Euler integral, in real part. -/
theorem twoShift_reflected_zeta_split {x : ℝ} (hx : 0 < x) :
    (twoShiftReflectedZeta x).re =
      (twoShiftLeftPole (1 / 2) x + twoShiftLeftPole (-1 / 2) x).re +
        reflectedIntegral570 (1 : DirichletCharacter ℂ 1) x := by
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let W := fun t : ℝ ↦ quarterKernel570.function (s t) * (x : ℂ) ^ s t
  let P := fun (p t : ℝ) ↦ (1 / (s t - (p : ℂ))) * W t
  let L := fun t : ℝ ↦ -logDeriv riemannZeta (w t) * W t
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hP (p : ℝ) (hne : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    simpa only [P, s, W, mul_assoc] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line quarterKernel570
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) hne hx
  have hL : MeasureTheory.Integrable L := by
    simpa only [L, W, s, w, DirichletCharacter.LFunction_modOne_eq, Complex.ofReal_neg, mul_neg,
      ← sub_eq_add_neg] using reflected_ordinary_integrable_570 (1 : DirichletCharacter ℂ 1) hx
  have hw (t : ℝ) : w t = 1 / 2 - s t := by
    dsimp only [w, s]; push_cast; ring
  have he (t : ℝ) :
    -(1 / w t + 1 / (w t - 1) + logDeriv riemannZeta (w t)) * W t =
      P (1 / 2) t + P (-1 / 2) t + L t := by
    dsimp only [P, L]
    rw [show w t = -(s t - ((1 / 2 : ℝ) : ℂ)) by
        rw [hw]; push_cast; ring,
      show -(s t - ((1 / 2 : ℝ) : ℂ)) - 1 = -(s t - ((-1 / 2 : ℝ) : ℂ)) by
        push_cast; ring]
    simp only [div_neg]
    ring
  have h1 := hP (1 / 2) (by norm_num only)
  have h2 := hP (-1 / 2) (by norm_num only)
  have hadd := MeasureTheory.integral_add (h1.add h2) hL
  simp only [Pi.add_apply] at hadd
  change
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, -(1 / w t + 1 / (w t - 1) + logDeriv riemannZeta (w t)) * W t).re =
      _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he), hadd,
    MeasureTheory.integral_add h1 h2, mul_add, mul_add, Complex.add_re]
  congr 1
  unfold reflectedIntegral570
  simp only [DirichletCharacter.LFunction_modOne_eq]
  dsimp only [L, W]
  simp_rw [hw]
  rfl

/-- At scale x at least one the reflected contribution after principal
subtraction is the principal-minus-character Euler integral, plus the zeta
zero sum and the two pole-line differences, minus the principal main term.
Both gamma factors have canceled before taking real parts. -/
theorem twoShift_reflected_euler_exact {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let P := fun p : ℝ ↦ twoShiftLeftPole p x - twoShiftCentralPole p x
    (reflectedArch570 χ x).re - reflectedIntegral570 χ x - (twoShiftXiPoles x).re =
      reflectedIntegral570 (1 : DirichletCharacter ℂ 1) x - reflectedIntegral570 χ x +
          (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ).re +
          (P (1 / 2) + P (-1 / 2)).re -
        (quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  intro P
  have hpos := zero_lt_one.trans_le hx
  have ha : reflectedArch570 χ x - twoShiftXiLeft x = twoShiftReflectedZeta x :=
    twoShift_reflected_gamma_cancel χ hn he hpos
  have h := twoShift_xi_error_exact hx
  rw [twoShift_xi_right_eq_left hRH hx] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.re ha
  rw [twoShift_reflected_zeta_split hpos] at h2
  dsimp only [P]
  simp only [Complex.sub_re, Complex.add_re] at h1 h2 ⊢
  linarith only [h1, h2]

/-- The inverse-scale prime-power weight at scale y. It is common to all
characters in the reflected formula. -/
noncomputable def twoShiftDualWeight (y : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n * (quarterKernel570.transform (((n : ℝ) * y)⁻¹)).re

private theorem dual_weight_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (twoShiftDualWeight y) (reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y) := by
  apply (reflected_hasSum_570 (1 : DirichletCharacter ℂ 1) hy).congr_fun
  intro n
  simp only [twoShiftDualWeight, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)),
    Complex.one_re, one_mul]

/-- If a character is one on primes through X, its reflected Euler deficit
at positive scale y is exactly the tail above floor X. The von Mangoldt
support removes all other prefix terms, including zero. -/
theorem twoShift_reflected_tail_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X y : ℝ}
    (hX : 0 ≤ X) (hy : 0 < y) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 χ y =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n }, (1 - (χ n.val).re) * twoShiftDualWeight y n.val := by
  have h := ((dual_weight_hasSum hy).sub (reflected_hasSum_570 χ hy)).tsum_eq
  rw [← h]
  let f := fun n : ℕ ↦ (1 - (χ n).re) * twoShiftDualWeight y n
  have hf (n : ℕ) : twoShiftDualWeight y n - (χ n).re * twoShiftDualWeight y n = f n := by
    dsimp only [f]
    ring
  change (∑' n : ℕ, (twoShiftDualWeight y n - (χ n).re * twoShiftDualWeight y n)) = _
  rw [tsum_congr hf]
  symm
  apply tsum_subtype_eq_of_support_subset (f := f) (s := {n : ℕ | ⌊X⌋₊ < n})
  intro n hn
  by_contra hno
  have hcut := (Nat.le_floor_iff hX).mp (le_of_not_gt hno)
  apply hn
  by_cases hm : ArithmeticFunction.vonMangoldt n = 0
  · simp only [f, twoShiftDualWeight, hm, zero_div, zero_mul, mul_zero]
  rw [show f n = (1 - (χ n).re) * twoShiftDualWeight y n from rfl,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hm,
    Complex.one_re, sub_self, zero_mul]

/-- For three characters with trace at least minus one and prime-prefix
passage, the reflected deficit is nonnegative and at most four times the
unsigned tail, as in (96.16). The trace bound is applied once to each term. -/
theorem twoShift_reflected_three_tail {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X y : ℝ}
    (hX : 0 ≤ X) (hy : 0 < y) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1) (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    let D := fun {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) ↦
      reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 χ y
    0 ≤ D a + D b + D c ∧
      D a + D b + D c ≤ 4 * ∑' n : { n : ℕ // ⌊X⌋₊ < n }, twoShiftDualWeight y n.val := by
  intro D
  let I := { n : ℕ // ⌊X⌋₊ < n }
  let f := fun n : I ↦ twoShiftDualWeight y n.val
  have hf : Summable f := (dual_weight_hasSum hy).summable.subtype _
  have hf0 (n : I) : 0 ≤ f n := by
    have hn : 0 < (n.val : ℝ) := Nat.cast_pos.mpr (Nat.zero_le _ |>.trans_lt n.property)
    exact
      mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (quarterKernel570.mellin_nonneg _ (inv_pos.mpr (mul_pos hn hy)))
  let g := fun {m : ℕ} (χ : DirichletCharacter ℂ m) (n : I) ↦ (1 - (χ n.val).re) * f n
  have hg {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) : Summable (g χ) := by
    have h := (dual_weight_hasSum hy).summable.sub (reflected_hasSum_570 χ hy).summable
    apply (h.subtype (fun n : ℕ ↦ ⌊X⌋₊ < n)).congr
    intro n
    change f n - (χ n.val).re * f n = (1 - (χ n.val).re) * f n
    ring
  have hsum := ((hg a).add (hg b)).tsum_add (hg c)
  rw [(hg a).tsum_add (hg b)] at hsum
  dsimp only [D]
  rw [twoShift_reflected_tail_eq a hX hy ha, twoShift_reflected_tail_eq b hX hy hb,
    twoShift_reflected_tail_eq c hX hy hc, ← hsum]
  have hterm (n : I) :
    g a n + g b n + g c n = (3 - ((a n.val).re + (b n.val).re + (c n.val).re)) * f n := by
    dsimp only [g]; ring
  constructor
  · apply tsum_nonneg
    intro n
    rw [hterm]
    exact
      mul_nonneg
        (by
          linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n.val),
            (Complex.re_le_norm _).trans (b.norm_le_one n.val),
            (Complex.re_le_norm _).trans (c.norm_le_one n.val)])
        (hf0 n)
  · rw [← tsum_mul_left]
    apply (((hg a).add (hg b)).add (hg c)).tsum_le_tsum _ (hf.mul_left 4)
    intro n
    change g a n + g b n + g c n ≤ 4 * f n
    rw [hterm]
    exact mul_le_mul_of_nonneg_right (by linarith only [ht n.val]) (hf0 n)

/-- At the shift by three, each dual weight has the polynomial density of
(96.22). The modulation by 14/5 leaves a logarithmic shift of minus 1/5. -/
theorem twoShift_dual_density {X : ℝ} (hx : 0 < X) (hy : 1 ≤ X * Real.exp (-3)) (n : ℕ) :
    twoShiftDualWeight (X * Real.exp (-3)) n =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) *
          Real.exp (-(51 / 50) * Real.log X)) *
        (ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity (Real.log X - 1 / 5) n) := by
  let y := X * Real.exp (-3)
  have hyp : 0 < y := zero_lt_one.trans_le hy
  have hr : 1 ≤ Real.sqrt y :=
    (Real.le_sqrt zero_le_one hyp.le).mpr (by simpa only [one_pow] using hy)
  have h := reflected_kernel_term_570 hr n
  rw [Real.sq_sqrt hyp.le, Real.rpow_def_of_pos (Real.sqrt_pos.mpr hyp), Real.log_sqrt hyp.le] at h
  have hl : Real.log y = Real.log X - 3 := by
    rw [show y = X * Real.exp (-3) from rfl, Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hl] at h
  change twoShiftDualWeight y n = _
  unfold twoShiftDualWeight
  rw [h]
  unfold reflectedWeight570 twoShiftReflectedDensity
  have he :
    Real.exp (-(51 / 50 : ℝ) * (14 / 5)) * Real.exp ((Real.log X - 3) / 2 * -(2 * (51 / 50))) =
      Real.exp ((51 / 50 : ℝ) * (1 / 5)) * Real.exp (-(51 / 50) * Real.log X) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 120 * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(38 / 25 : ℝ)) *
        (Real.log n + (Real.log X - 1 / 5)) ^ 5) *
      he

/-- At all high cutoffs under RH the unsigned dual tail at the shift by
three costs less than 0.005262. The exact density identity permits direct
use of the certified reflected Abel estimate. -/
theorem twoShift_dual_tail_numeric (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X) :
    (∑' n : { n : ℕ // ⌊X⌋₊ < n }, twoShiftDualWeight (X * Real.exp (-3)) n.val) <
      5262 / 1000000 := by
  have hx : 0 < X := by linarith only [hX]
  have hex := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have hy : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul,
      show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [hex, hX]
  rw [tsum_congr (fun n : { n : ℕ // ⌊X⌋₊ < n } ↦ twoShift_dual_density hx hy n.val), tsum_mul_left,
    mul_assoc]
  exact twoShiftReflectedTail_numeric hRH hX

/-- For three prefix-trivial characters with trace at least minus one, the
half-weighted change of their reflected Euler deficits exceeds -0.010524.
Keep the nonnegative first scale and apply (96.22) at the second scale. -/
theorem twoShift_dual_difference_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → a n = 1) (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ X → c n = 1) :
    let D := fun (y : ℝ) ↦
      3 * reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y -
        (reflectedIntegral570 a y + reflectedIntegral570 b y + reflectedIntegral570 c y)
    (-10524 / 1000000 : ℝ) < (D (X * Real.exp (-(14 / 5))) - D (X * Real.exp (-3))) / 2 := by
  intro D
  have hx : 0 < X := by linarith only [hX]
  have h1 :=
    (twoShift_reflected_three_tail a b c hx.le (mul_pos hx (Real.exp_pos (-(14 / 5)))) ht ha hb
        hc).1
  have h2 :=
    (twoShift_reflected_three_tail a b c hx.le (mul_pos hx (Real.exp_pos (-3))) ht ha hb hc).2
  dsimp only [D]
  linarith only [h1, h2, twoShift_dual_tail_numeric hRH hX]

/-- Moving the positive pole integral from the left line to the imaginary
axis crosses no pole. The sixth-order kernel is regular at -1/2; its actual
pole at -51/50 is strictly left of the entire rectangle. -/
theorem twoShift_left_positive_pole {x : ℝ} (hx : 1 ≤ x) :
    twoShiftLeftPole (1 / 2) x = twoShiftCentralPole (1 / 2) x := by
  let a : ℝ := -9 / 16
  let p : ℝ := 1 / 2
  let K := quarterKernel570
  let F := fun s : ℂ ↦ (1 / (s - (p : ℂ))) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hl : -1 / 2 - K.delta < a := by
    rw [hd]; norm_num only [a]
  have hu : (0 : ℝ) ≤ 1 / 2 + K.delta := by
    rw [hd]; norm_num only
  have ha : a ≤ 0 := by norm_num only [a]
  have hxp := zero_lt_one.trans_le hx
  have hi0 :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K (hl.trans_le ha) hu
      (by norm_num only) (by norm_num only [p] : (0 : ℝ) ≠ p) hxp
  have hia :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hl (ha.trans hu)
      (by norm_num only [a]) (by norm_num only [p, a] : a ≠ p) hxp
  have ht := LLS.PaperStatements.MellinKernel.tendsto_pole_horizontalIntegral K ha hl hu hx p
  have hlim :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K := F) (a := a) (b := 0) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          ht (-1) (Or.inr rfl))
      (by simpa only [F, T, one_mul] using ht 1 (Or.inl rfl))
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hia)
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hi0)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((a : ℂ) - T n * Complex.I)
        (((0 : ℝ) : ℂ) + T n * Complex.I) =
      0 := by
    apply AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_zero_of_holomorphic
    intro z hz
    have hr := hz.1
    change z.re ∈ Set.uIcc _ _ at hr
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Set.uIcc_of_le ha,
      Set.mem_Icc] at hr
    have hden : z - (p : ℂ) ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re, p] at hh
      linarith only [hr.2, hh]
    have hk : DifferentiableAt ℂ K.function z := by
      change DifferentiableAt ℂ (Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5)) z
      unfold Analysis.rationalPoleFunction
      have hn : 1 + 2 * ((25 / 51 : ℝ) : ℂ) * z ≠ 0 := by
        intro h
        have hh := congrArg Complex.re h
        norm_num only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.im_ofNat, Complex.re_ofNat, Complex.zero_re,
          Complex.one_re] at hh
        dsimp only [a] at hr
        linarith only [hr.1, hh]
      fun_prop (disch := exact pow_ne_zero _ hn)
    exact
      (((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (p : ℂ)) hden).mul
            hk |>.mul
          ((differentiable_id.const_cpow
              (Or.inl
                (Complex.ofReal_ne_zero.mpr hxp.ne'))).differentiableAt)).differentiableWithinAt
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left Complex.I_ne_zero)
  apply congrArg (fun u : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * u)
  simpa only [F, Complex.ofReal_zero, zero_add, mul_comm Complex.I, mul_assoc] using he.symm

/-- In the reflected explicit formula only the negative pole contributes a
left-to-central contour difference. The positive pole cancels at each scale. -/
theorem twoShift_reflected_single_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (reflectedArch570 χ x).re - reflectedIntegral570 χ x - (twoShiftXiPoles x).re =
      reflectedIntegral570 (1 : DirichletCharacter ℂ 1) x - reflectedIntegral570 χ x +
          (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ).re +
          (twoShiftLeftPole (-1 / 2) x - twoShiftCentralPole (-1 / 2) x).re -
        (quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  have h := twoShift_reflected_euler_exact χ hn he hRH hx
  dsimp only at h
  simpa only [twoShift_left_positive_pole hx, sub_self, zero_add] using h

/-- Crossing the negative half-unit pole subtracts its unnormalized kernel
value times the scale power from the central integral. The residue is
positive in the central-minus-left orientation. -/
theorem twoShift_left_negative_pole {x : ℝ} (hx : 1 ≤ x) :
    twoShiftLeftPole (-1 / 2) x - twoShiftCentralPole (-1 / 2) x =
      -(quarterKernel570.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)) := by
  let a : ℝ := -9 / 16
  let p : ℝ := -1 / 2
  let K := quarterKernel570
  let F := fun s : ℂ ↦ (1 / (s - (p : ℂ))) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hl : -1 / 2 - K.delta < a := by
    rw [hd]; norm_num only [a]
  have hu : (0 : ℝ) ≤ 1 / 2 + K.delta := by
    rw [hd]; norm_num only
  have ha : a ≤ 0 := by norm_num only [a]
  have hxp := zero_lt_one.trans_le hx
  have hi0 :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K (hl.trans_le ha) hu
      (by norm_num only) (by norm_num only [p] : (0 : ℝ) ≠ p) hxp
  have hia :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hl (ha.trans hu)
      (by norm_num only [a]) (by norm_num only [p, a] : a ≠ p) hxp
  have ht := LLS.PaperStatements.MellinKernel.tendsto_pole_horizontalIntegral K ha hl hu hx p
  have hlim :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K := F) (a := a) (b := 0) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          ht (-1) (Or.inr rfl))
      (by simpa only [F, T, one_mul] using ht 1 (Or.inl rfl))
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hia)
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hi0)
  let H := fun z : ℂ ↦ K.function z * (x : ℂ) ^ z
  have hH (z : ℂ) (hr : a ≤ z.re) : AnalyticAt ℂ H z := by
    change
      AnalyticAt ℂ (fun u ↦ Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5) u * (x : ℂ) ^ u) z
    unfold Analysis.rationalPoleFunction
    have hn : 1 + 2 * ((25 / 51 : ℝ) : ℂ) * z ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      norm_num only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.im_ofNat, Complex.re_ofNat, Complex.zero_re,
        Complex.one_re] at hh
      dsimp only [a] at hr
      linarith only [hr, hh]
    fun_prop (disch :=
      first
      | exact pow_ne_zero _ hn
      | exact Complex.ofReal_mem_slitPlane.mpr hxp)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((a : ℂ) - T n * Complex.I)
        (((0 : ℝ) : ℂ) + T n * Complex.I) =
      2 * Real.pi * Complex.I * H (p : ℂ) := by
    have htpos : 0 < T n := by
      dsimp only [T]; linarith only [Nat.cast_nonneg (α := ℝ) n]
    have ho :
      (p : ℂ) ∈
        AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox ((a : ℂ) - T n * Complex.I)
          (((0 : ℝ) : ℂ) + T n * Complex.I) := by
      change ((_ < _ ∧ _ < _) ∧ (_ < _ ∧ _ < _))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.sub_im,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub, min_eq_left ha,
        max_eq_right ha, min_eq_left (neg_le_self htpos.le), max_eq_right (neg_le_self htpos.le)]
      exact ⟨⟨by norm_num only [a, p], by norm_num only [p]⟩, neg_lt_zero.mpr htpos, htpos⟩
    apply
      AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_simple_pole
        (by
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero]
          norm_num only [a])
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add,
            zero_sub] using neg_lt_self htpos)
        ho
    · intro z hbox hne
      have hr := hbox.1
      change z.re ∈ Set.uIcc _ _ at hr
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Set.uIcc_of_le ha,
        Set.mem_Icc] at hr
      simp only [F, mul_assoc]
      exact
        ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (p : ℂ))
              (sub_ne_zero.mpr hne)).mul
          (hH z hr.1).differentiableAt
    · exact hH _ (by norm_num only [a, p, Complex.ofReal_re])
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hn : z ≠ (p : ℂ) := hz
      dsimp only [F, H]
      rw [← mul_assoc, ← mul_assoc, one_div, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u ↦ d * u) he
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  change twoShiftLeftPole p x - twoShiftCentralPole p x = -H (p : ℂ)
  rw [← neg_sub]
  apply congrArg Neg.neg
  simpa only [twoShiftLeftPole, twoShiftCentralPole, F, Complex.ofReal_zero, zero_add,
    mul_comm Complex.I, mul_assoc] using hh

/-- For a nonprincipal even character under RH and a scale at least one, the
reflected correction equals the difference of reflected Euler integrals plus
the zeta zero sum, less the kernel values weighted at both half-unit poles. -/
theorem twoShift_reflected_residues {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (reflectedArch570 χ x).re - reflectedIntegral570 χ x - (twoShiftXiPoles x).re =
      reflectedIntegral570 (1 : DirichletCharacter ℂ 1) x - reflectedIntegral570 χ x +
          (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ).re -
        (quarterKernel570.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
        (quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re := by
  simpa only [twoShift_left_negative_pole hx, Complex.neg_re, sub_eq_add_neg] using
    twoShift_reflected_single_pole χ hn he hRH hx

/-- The real expression for one shifted scale after evaluating both residues.
It includes the conductor term, the reflected Euler integrals and the zeta zeros. -/
noncomputable def twoShiftResidueValue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) :
    ℝ :=
  (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹ : ℂ)).re +
    (reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 χ y +
        (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm y ρ).re -
      (quarterKernel570.function ((-1 / 2 : ℝ) : ℂ) * (y : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
      (quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (y : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re)

/-- Under GRH the two shifted zero sums of a primitive even self-inverse nonprincipal
character trivial on primes through X differ by the exact residue-value difference,
provided the smaller shifted scale is at least one. -/
theorem twoShift_zero_residue_difference {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprim : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {X : ℝ} (hx : 0 < X)
    (hcut : 1 ≤ X * Real.exp (-3)) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let Z := fun y : ℝ ↦ (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ y ρ).re
    Z B - Z T = twoShiftResidueValue χ B - twoShiftResidueValue χ T := by
  intro B T Z
  have hb : 1 ≤ B :=
    hcut.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only)) hx.le)
  have hz := twoShift_even_zero_difference hq hG hprim hn (hi.trans_ne hn) he hx hcut hp
  dsimp only at hz
  rw [hi] at hz
  dsimp only [twoShiftResidueValue, B, T, Z]
  linarith only [hz, twoShift_reflected_residues χ hn he hG.riemann hb,
    twoShift_reflected_residues χ hn he hG.riemann hcut]

/-- For an odd prime pair in a squarefree Korselt integer, equal two-adic valuations
and passage of every eligible prime identify the pair's shifted zero difference
with the explicit residue difference under GRH. -/
theorem pair_twoShift_residue_difference {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero (p * q)] [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n)
    (ho : Odd n) (hs : Squarefree n) (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hk : p - 1 ∣ n - 1)
    (hj : q - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hx : 0 < X)
    (hcut : 1 ≤ X * Real.exp (-3))
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let Z := fun y : ℝ ↦ (∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ y ρ).re
    Z B - Z T = twoShiftResidueValue χ B - twoShiftResidueValue χ T := by
  have hprod :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  apply
    twoShift_zero_residue_difference hprod hG (pair_character_primitive hs hd (hp.mul hq))
      (pair_character_ne_one hs hd (hp.mul hq) hprod)
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hp hq hk hj hv) hx hcut
  intro l hl hbound
  exact
    pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right p q).trans hd)
      ((dvd_mul_left q p).trans hd) hd hk hj hv l (hpass l hl hbound)

/-- The prime-sum upper bound obtained by inserting the exact shifted residues
into the two-frequency inequality. Both cosine sums and the mass term use X. -/
noncomputable def twoShiftResidueBudget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) :
    ℝ :=
  let W := fun s : ℝ ↦ ∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (s * ρ.im)
  contourNonEuler570 χ X - reflectedIntegral570 χ X + quarterMass570 χ -
      (W (14 / 5) - W 3 + twoShiftResidueValue χ (X * Real.exp (-(14 / 5))) -
          twoShiftResidueValue χ (X * Real.exp (-3))) /
        2 +
    (quarterMass570 χ - W (1 / 5)) / 4

/-- Under GRH and prime passage through X, the arithmetic sum for a pair Jacobi
character is bounded by its residue budget, with no approximation of the poles. -/
theorem pair_twoShift_residue_upper {n p q : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero (p * q)]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n)
    (hs : Squarefree n) (hp : Odd p) (hq : Odd q) (hd : p * q ∣ n) (hk : p - 1 ∣ n - 1)
    (hj : q - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hx : 0 < X)
    (hcut : 1 ≤ X * Real.exp (-3))
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    (∑' k : ℕ, quarterKernel570.summand χ X k).re ≤ twoShiftResidueBudget χ X := by
  intro χ
  have hm :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hprim := pair_character_primitive hs hd (hp.mul hq)
  have hne := pair_character_ne_one hs hd (hp.mul hq) hm
  have hX : 1 ≤ X :=
    hcut.trans (mul_le_of_le_one_right hx.le (Real.exp_le_one_iff.mpr (by norm_num only)))
  have hz := pair_twoShift_residue_difference hn ho hs hp hq hd hk hj hv hG hx hcut hpass
  have hw := quarter_zero_shifted_lower hm hG hprim hne (inv_ne_one.mpr hne) hx (14 / 5) 3 (1 / 2)
  dsimp only at hw hz
  rw [show (3 : ℝ) - 14 / 5 = 1 / 5 by norm_num only,
    zero_re_eq_contour_sub_prime hm hG hprim hne (inv_ne_one.mpr hne) hX] at hw
  dsimp only [twoShiftResidueBudget, χ]
  linarith only [hw, hz]

/-- Under universal prime passage, the sum for the three pair characters is bounded by
the sum of the exact residue budgets at the common cutoff. -/
theorem twoShift_triple_residue_upper {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hx : 0 < X)
    (hcut : 1 ≤ X * Real.exp (-3))
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    (∑' n : ℕ, quarterKernel570.summand a X n).re + (∑' n : ℕ, quarterKernel570.summand b X n).re +
        (∑' n : ℕ, quarterKernel570.summand c X n).re ≤
      twoShiftResidueBudget a X + twoShiftResidueBudget b X + twoShiftResidueBudget c X := by
  intro a b c
  have ha := pair_twoShift_residue_upper hn ho hsq hp hq hpq hpk hqk hvq hG hx hcut hpass
  have hb := pair_twoShift_residue_upper hn ho hsq hp hr hpr hpk hrk hvr hG hx hcut hpass
  have hc :=
    pair_twoShift_residue_upper hn ho hsq hq hr hqr hqk hrk (hvr.trans hvq.symm) hG hx hcut hpass
  dsimp only at ha hb hc
  dsimp only [a, b, c]
  linarith only [ha, hb, hc]

/-- A strict gap between the exact residue budgets and the principal prefix with squares
forces a rejecting prime at or below X for the three uniform Korselt pairs. -/
theorem twoShift_witness_of_residue_gap {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hgap :
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
        let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
        let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
        let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
        let f := fun k : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re
        let S := (Finset.Ioc 0 ⌊X⌋₊).filter (fun k : ℕ ↦ X < (k : ℝ) ^ 2)
        twoShiftResidueBudget a X + twoShiftResidueBudget b X + twoShiftResidueBudget c X <
          4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) -
            (∑' k : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X k).re) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_contra hnone
  have hpass (l : ℕ) (hl : l.Prime) (hx : (l : ℝ) ≤ X) :
    PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
    Classical.byContradiction (fun hf ↦ hnone ⟨l, hl, hx, hf⟩)
  have hx : 0 < X := by linarith only [hX]
  have hex := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have ht : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul,
      show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [hex, hX]
  have hu :=
    twoShift_triple_residue_upper hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hx ht hpass
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  let S := (Finset.Ioc 0 ⌊X⌋₊).filter (fun k : ℕ ↦ X < (k : ℝ) ^ 2)
  have hs (k : ℕ) (hk : k ∈ S) : (k : ℝ) ≤ X ∧ X < (k : ℝ) ^ 2 :=
    ⟨(Nat.le_floor_iff hx.le).mp (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).2,
      (Finset.mem_filter.mp hk).2⟩
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hl :=
    kernel_prefix_add_squares quarterKernel570 a b c hx S hs ht
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right p q).trans hpq)
          ((dvd_mul_left q p).trans hpq) hpq hpk hqk hvq l (hpass l hl hlX))
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hp hr ((dvd_mul_right p r).trans hpr)
          ((dvd_mul_left r p).trans hpr) hpr hpk hrk hvr l (hpass l hl hlX))
      (fun l hl hlX ↦
        pair_character_nat_eq_one hn ho hq hr ((dvd_mul_right q r).trans hqr)
          ((dvd_mul_left r q).trans hqr) hqr hqk hrk (hvr.trans hvq.symm) l (hpass l hl hlX))
  exact (not_lt_of_ge (hl.trans hu)) (hgap hpass)

/-- The common part of the three residue values at scale y for a triple of product n.
The pair conductors contribute twice log n, and each zeta zero and pole occurs three times. -/
noncomputable def twoShiftTripleMain (n : ℕ) (y : ℝ) : ℝ :=
  2 * Real.log n * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹ +
    3 *
      ((∑' ρ, quarterKernel570.zetaOscillatingZeroTerm y ρ).re -
        (quarterKernel570.function ((-1 / 2 : ℝ) : ℂ) * (y : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
        (quarterKernel570.function ((1 / 2 : ℝ) : ℂ) * (y : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re)

/-- At each positive scale the sum of the pair residues exceeds the common main term
by a nonnegative quantity bounded by four times the unsigned reflected tail, assuming
the trace bound and triviality of all three characters at primes through X. -/
theorem twoShift_triple_residue_error {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) {X y : ℝ} (hX : 0 ≤ X) (hy : 0 < y)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    let E :=
      twoShiftResidueValue a y + twoShiftResidueValue b y + twoShiftResidueValue c y -
        twoShiftTripleMain n y
    0 ≤ E ∧ E ≤ 4 * ∑' k : { k : ℕ // ⌊X⌋₊ < k }, twoShiftDualWeight y k.val := by
  intro E
  have h := twoShift_reflected_three_tail a b c hX hy ht ha hb hc
  dsimp only at h
  have he :
    E =
      (reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 a y) +
        (reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 b y) +
        (reflectedIntegral570 (1 : DirichletCharacter ℂ 1) y - reflectedIntegral570 c y) := by
    simp only [E, twoShiftResidueValue, twoShiftTripleMain, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re, Complex.norm_natCast]
    linear_combination
      (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹) * pair_level_log_sum hn
  rw [he]
  exact h

/-- Under RH, for X at least 85264, replacing the three half-weighted residue differences
by the common main difference loses less than 0.010524. Only the smaller scale needs
a numerical tail bound, since the error at the larger scale is nonnegative. -/
theorem twoShift_triple_residue_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let R := fun y ↦ twoShiftResidueValue a y + twoShiftResidueValue b y + twoShiftResidueValue c y
    (twoShiftTripleMain n B - twoShiftTripleMain n T) / 2 - 10524 / 1000000 < (R B - R T) / 2 := by
  intro B T R
  have hx : 0 < X := by linarith only [hX]
  have hB :=
    (twoShift_triple_residue_error hn a b c hx.le (mul_pos hx (Real.exp_pos (-(14 / 5)))) ht ha hb
        hc).1
  have hT :=
    (twoShift_triple_residue_error hn a b c hx.le (mul_pos hx (Real.exp_pos (-3))) ht ha hb hc).2
  dsimp only [B, T, R]
  linarith only [hB, hT, twoShift_dual_tail_numeric hRH hX]

/-- The part of the two-frequency prime-sum bound independent of shifted residue values.
The cosine sums at 14/5, 3 and 1/5 use the zero mass at the original scale X. -/
noncomputable def twoShiftCosineBudget {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ) :
    ℝ :=
  let W := fun s : ℝ ↦ ∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (s * ρ.im)
  contourNonEuler570 χ X - reflectedIntegral570 χ X + quarterMass570 χ - (W (14 / 5) - W 3) / 2 +
    (quarterMass570 χ - W (1 / 5)) / 4

/-- The three residue budgets are strictly below the three cosine budgets less the
common shifted main contribution plus 0.010524 at every high cutoff under RH. -/
theorem twoShift_triple_budget_lt {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    twoShiftResidueBudget a X + twoShiftResidueBudget b X + twoShiftResidueBudget c X <
      twoShiftCosineBudget a X + twoShiftCosineBudget b X + twoShiftCosineBudget c X -
          (twoShiftTripleMain n (X * Real.exp (-(14 / 5))) -
              twoShiftTripleMain n (X * Real.exp (-3))) /
            2 +
        10524 / 1000000 := by
  have h := twoShift_triple_residue_lower hn a b c hRH hX ht ha hb hc
  dsimp only at h
  dsimp only [twoShiftResidueBudget, twoShiftCosineBudget]
  linarith only [h]

private theorem twoShift_kernel_real (s : ℝ) :
    (quarterKernel570.function (s : ℂ)).re =
      (50 / 51) * Real.exp (2 * (7 / 5) * s) / (1 + 2 * (25 / 51) * s) ^ 6 := by
  have h :
    quarterKernel570.function (s : ℂ) =
      (((50 / 51) * Real.exp (2 * (7 / 5) * s) / (1 + 2 * (25 / 51) * s) ^ 6 : ℝ) : ℂ) := by
    change Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5) (s : ℂ) = _
    unfold Analysis.rationalPoleFunction
    push_cast
    norm_num only
  rw [h, Complex.ofReal_re]

/-- The conductor and two real pole contributions at a positive scale. The kernel
at a real pole s contributes its real value times the real power y^s. -/
noncomputable def twoShiftRealMain (n : ℕ) (y : ℝ) : ℝ :=
  2 * Real.log n * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹ -
    3 *
      ((50 / 51) * Real.exp (-(7 / 5)) / (1 - 25 / 51) ^ 6 * y ^ (-1 / 2 : ℝ) +
        (50 / 51) * Real.exp (7 / 5) / (1 + 25 / 51) ^ 6 * y ^ (1 / 2 : ℝ))

/-- At a positive scale the difference between the common triple main term and
its real conductor and pole expression is three times the zeta zero sum in real part. -/
theorem twoShift_triple_main_eq (n : ℕ) {y : ℝ} (hy : 0 < y) :
    twoShiftTripleMain n y =
      twoShiftRealMain n y + 3 * (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm y ρ).re := by
  simp only [twoShiftTripleMain, twoShiftRealMain, ← Complex.ofReal_cpow hy.le, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [twoShift_kernel_real, twoShift_kernel_real]
  norm_num only
  ring

/-- Under RH the weighted zeta contribution at two positive scales costs at most
0.00024. Including the reflected tail gives the combined allowance 0.010764. -/
theorem twoShift_real_budget_le (n : ℕ) (C : ℝ) (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) :
    C - (twoShiftTripleMain n x - twoShiftTripleMain n y) / 2 + 10524 / 1000000 ≤
      C - (twoShiftRealMain n x - twoShiftRealMain n y) / 2 + 10764 / 1000000 := by
  have h := (Complex.abs_re_le_norm _).trans (twoShift_zeta_sum_diff_bound hRH hx hy)
  rw [Complex.sub_re] at h
  rw [twoShift_triple_main_eq n hx, twoShift_triple_main_eq n hy]
  linarith only [(abs_le.mp h).1]

/-- The fixed cosine multiplier on the sixth-pole zero mass after the two-frequency
phase estimate. Its four frequencies are zero, 1/5, 14/5 and 3. -/
noncomputable def twoShiftCosineWeight (t : ℝ) : ℝ :=
  1 - (Real.cos (14 / 5 * t) - Real.cos (3 * t)) / 2 + (1 - Real.cos (1 / 5 * t)) / 4

/-- The signed sixth-pole zero mass weighted by the fixed cosine multiplier.
Each ordinate is counted with the divisor multiplicity of the completed L-function. -/
noncomputable def twoShiftCosineMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ((51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + ρ.im ^ 2) ^ 3) *
      twoShiftCosineWeight ρ.im

/-- The cosine budget consists of the original contour correction and one
cutoff-independent zero sum with divisor multiplicities and the fixed cosine weight. -/
theorem twoShift_cosine_budget_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X : ℝ} (hx : 0 < X) :
    twoShiftCosineBudget χ X =
      contourNonEuler570 χ X - reflectedIntegral570 χ X + twoShiftCosineMass χ := by
  let f := fun ρ : ℂ ↦ ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖
  let w := fun (s : ℝ) (ρ : ℂ) ↦ f ρ * Real.cos (s * ρ.im)
  have hf : Summable f :=
    (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel570 hq hG hp hn
        (inv_ne_one.mpr hn) hx).norm
  have hw (s : ℝ) : Summable (w s) := by
    apply hf.of_norm_bounded
    intro ρ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact
      mul_le_of_le_one_right (norm_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have he (ρ : ℂ) : f ρ = _ :=
    (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ hx ρ).trans
      (kernel_zero_norm_570 hn ρ)
  have hm : quarterMass570 χ = ∑' ρ, f ρ := (tsum_congr he).symm
  have hsplit (ρ : ℂ) :
    f ρ * twoShiftCosineWeight ρ.im =
      f ρ - (w (14 / 5) ρ - w 3 ρ) * (1 / 2) + (f ρ - w (1 / 5) ρ) * (1 / 4) := by
    dsimp only [w, twoShiftCosineWeight]
    ring
  unfold twoShiftCosineMass
  simp_rw [← quarter_zero_norm_570, ← he, hsplit]
  rw [(((hf.sub (((hw (14 / 5)).sub (hw 3)).mul_right (1 / 2)))).tsum_add
      ((hf.sub (hw (1 / 5))).mul_right (1 / 4))),
    hf.tsum_sub, tsum_mul_right, tsum_mul_right, (hw (14 / 5)).tsum_sub (hw 3),
    hf.tsum_sub (hw (1 / 5))]
  · unfold twoShiftCosineBudget
    rw [hm]
    dsimp only [w, f]
    ring
  · exact ((hw (14 / 5)).sub (hw 3)).mul_right _

/-- For a pair of odd prime factors of a squarefree integer, the exact contour budget
uses the fixed cosine mass at every positive cutoff under GRH. -/
theorem pair_twoShift_cosine_budget {n p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] [Fact q.Prime]
    (hs : Squarefree n) (hd : p * q ∣ n) (ho : Odd (p * q))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hx : 0 < X) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) ho
    twoShiftCosineBudget χ X =
      contourNonEuler570 χ X - reflectedIntegral570 χ X + twoShiftCosineMass χ := by
  have hm :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  exact
    twoShift_cosine_budget_eq hm hG (pair_character_primitive hs hd ho)
      (pair_character_ne_one hs hd ho hm) hx

/-- Zeta contribution of the cosine correction after the unmodulated mass has
been removed. The same correction occurs for each of the three characters. -/
noncomputable def twoShiftZetaCosineCorrection : ℝ :=
  ∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖ * (twoShiftCosineWeight (ρ : ℂ).im - 1)

/-- The cosine correction has absolute value less than 3/25000 under RH,
since its multiplier lies between minus one and three halves. -/
theorem twoShift_zeta_cosine_bound (hRH : RiemannHypothesis) :
    |twoShiftZetaCosineCorrection| < 3 / 25000 := by
  let f := fun ρ ↦ ‖quarterKernel570.zetaKernelZeroTerm ρ‖
  have hw (t : ℝ) : |twoShiftCosineWeight t - 1| ≤ 3 / 2 := by
    unfold twoShiftCosineWeight
    apply abs_le.mpr
    constructor <;>
      linarith only [Real.cos_le_one (14 / 5 * t), Real.neg_one_le_cos (14 / 5 * t),
        Real.cos_le_one (3 * t), Real.neg_one_le_cos (3 * t), Real.cos_le_one (1 / 5 * t),
        Real.neg_one_le_cos (1 / 5 * t)]
  have hs : Summable f :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel570 hRH).norm
  have hb (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖f ρ * (twoShiftCosineWeight (ρ : ℂ).im - 1)‖ ≤ f ρ * (3 / 2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _)
  have hg := (hs.mul_right (3 / 2)).of_norm_bounded hb
  have h := (norm_tsum_le_tsum_norm hg.norm).trans (hg.norm.tsum_le_tsum hb (hs.mul_right _))
  rw [tsum_mul_right, Real.norm_eq_abs] at h
  change
    |twoShiftZetaCosineCorrection| ≤ (∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖) * (3 / 2) at h
  linarith only [h, twoShift_zeta_mass_small hRH]

/-- Replacing the fixed-frequency zeta correction by its certified bound costs
0.00036 across the three pairs, giving 0.011124 together with the shifted terms. -/
theorem twoShift_zeta_comparison_le (hRH : RiemannHypothesis) (C : ℝ) :
    C + 10764 / 1000000 ≤ C - 3 * twoShiftZetaCosineCorrection + 11124 / 1000000 := by
  linarith only [(abs_lt.mp (twoShift_zeta_cosine_bound hRH)).2]

/-- The even rational function whose restriction to the imaginary axis equals the
sixth-pole norm. Its only poles are the two real points ±51/50, each of order three. -/
noncomputable def twoShiftSymmetricKernel (z : ℂ) : ℂ :=
  (51 / 50 : ℂ) ^ 5 / (((51 / 50 : ℂ) - z) * ((51 / 50 : ℂ) + z)) ^ 3

/-- On the imaginary axis the symmetric rational function is the real sixth-pole
weight, including its normalization. -/
theorem twoShift_symmetric_axis (t : ℝ) :
    twoShiftSymmetricKernel (Complex.I * t) =
      (((51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + t ^ 2) ^ 3 : ℝ) : ℂ) := by
  unfold twoShiftSymmetricKernel
  push_cast
  rw [show ((51 / 50 : ℂ) - Complex.I * t) * (51 / 50 + Complex.I * t) = (51 / 50) ^ 2 + (t : ℂ) ^ 2
      by
      rw [mul_comm, ← sq_sub_sq, mul_pow, Complex.I_sq]
      ring]

/-- The symmetric weight splits into first, second and third powers at each pole.
This decomposition gives the quadratic polynomial in the exponential Mellin profile. -/
theorem twoShift_symmetric_fractions {z : ℂ} (hm : (51 / 50 : ℂ) - z ≠ 0)
    (hp : (51 / 50 : ℂ) + z ≠ 0) :
    let a := (51 / 50 : ℂ)
    let F := fun u : ℂ ↦ (3 / 16) / u + (3 * a / 16) / u ^ 2 + (a ^ 2 / 8) / u ^ 3
    twoShiftSymmetricKernel z = F (a - z) + F (a + z) := by
  dsimp only [twoShiftSymmetricKernel]
  generalize (51 / 50 : ℂ) = a at hm hp ⊢
  rw [mul_pow]
  field_simp [hm, hp]
  ring

/-- The symmetric test kernel multiplied by the four exponential shifts.
Taking real parts on the imaginary axis recovers the cosine multiplier. -/
noncomputable def twoShiftCosineKernel (z : ℂ) : ℂ :=
  twoShiftSymmetricKernel z *
    (1 - (Complex.exp ((14 / 5 : ℝ) * z) - Complex.exp ((3 : ℝ) * z)) / 2 +
      (1 - Complex.exp ((1 / 5 : ℝ) * z)) / 4)

private theorem twoShift_exp_axis (s t : ℝ) :
    (Complex.exp ((s : ℂ) * (Complex.I * t))).re = Real.cos (s * t) := by
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, add_zero, one_mul,
    Real.exp_zero]

/-- The character spectral term is the divisor sum of the real part of one
analytic test function, in the form needed for the zeta contour comparison. -/
theorem twoShift_cosine_mass_kernel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    twoShiftCosineMass χ =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (twoShiftCosineKernel (Complex.I * ρ.im)).re := by
  apply tsum_congr
  intro ρ
  rw [twoShiftCosineKernel, twoShift_symmetric_axis, Complex.re_ofReal_mul]
  simp only [twoShiftCosineWeight, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.div_ofNat_re, twoShift_exp_axis, mul_assoc]

/-- On the principal side the same analytic shifts are used with the unshifted
symmetric kernel subtracted. This expresses the zeta correction with its actual
zero multiplicities for comparison to the character divisor sums. -/
theorem twoShift_zeta_cosine_kernel :
    twoShiftZetaCosineCorrection =
      ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
        (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) *
          (twoShiftCosineKernel (Complex.I * (ρ : ℂ).im) -
              twoShiftSymmetricKernel (Complex.I * (ρ : ℂ).im)).re := by
  apply tsum_congr
  intro ρ
  rw [LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, norm_mul, Complex.norm_natCast,
    quarter_zero_norm_570, Complex.sub_re, twoShiftCosineKernel, twoShift_symmetric_axis,
    Complex.re_ofReal_mul, Complex.ofReal_re]
  simp only [twoShiftCosineWeight, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.div_ofNat_re, twoShift_exp_axis]
  ring

/-- The one-sided half of the symmetric Mellin profile. The three log powers
give the simple, double and triple poles, and the power of u translates them to -51/50. -/
noncomputable def twoShiftHalfProfile (u : ℝ) : ℂ :=
  (u : ℂ) ^ (51 / 50 : ℂ) •
    ((3 / 16 : ℂ) • Analysis.mellinLogPowerWeight 0 u +
      (3 * (51 / 50) / 16 : ℂ) • Analysis.mellinLogPowerWeight 1 u +
      ((51 / 50) ^ 2 / 16 : ℂ) • Analysis.mellinLogPowerWeight 2 u)

private theorem twoShift_mellin_add {f g : ℝ → ℂ} {s a b : ℂ} (hf : HasMellin f s a)
    (hg : HasMellin g s b) : HasMellin (fun u ↦ f u + g u) s (a + b) := by
  rw [← hf.2, ← hg.2]
  exact hasMellin_add hf.1 hg.1

private theorem twoShift_mellin_log (k : ℕ) (c : ℂ) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun u ↦ c • Analysis.mellinLogPowerWeight k u) s
      (c * ((k.factorial : ℂ) / s ^ (k + 1))) := by
  have h := Analysis.hasMellin_logPowerWeight k hs
  simpa only [h.2, smul_eq_mul] using hasMellin_const_smul h.1 c

/-- On the open right half-plane translated by -51/50, the one-sided profile
has the three convergent Mellin moments appearing in the partial fractions. -/
theorem twoShift_half_hasMellin {s : ℂ} (hs : 0 < (s + 51 / 50).re) :
    let u := s + 51 / 50
    HasMellin twoShiftHalfProfile s
      ((3 / 16) / u + (3 * (51 / 50) / 16) / u ^ 2 + ((51 / 50) ^ 2 / 8) / u ^ 3) := by
  intro u
  have h :=
    twoShift_mellin_add
      (twoShift_mellin_add (twoShift_mellin_log 0 (3 / 16) hs)
        (twoShift_mellin_log 1 (3 * (51 / 50) / 16) hs))
      (twoShift_mellin_log 2 ((51 / 50) ^ 2 / 16) hs)
  refine ⟨MellinConvergent.cpow_smul.mpr h.1, ?_⟩
  unfold twoShiftHalfProfile
  rw [mellin_cpow_smul, h.2]
  dsimp only [u]
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, pow_one]
  ring

/-- Throughout the open strip between the two poles the symmetric kernel is the
Mellin transform of the one-sided profile plus its reflection under inversion.
Both integrals converge separately on this strip. -/
theorem twoShift_symmetric_hasMellin {s : ℂ} (hl : -(51 / 50 : ℝ) < s.re) (hu : s.re < 51 / 50) :
    HasMellin (fun u ↦ twoShiftHalfProfile u + twoShiftHalfProfile u⁻¹) s
      (twoShiftSymmetricKernel s) := by
  have hp : 0 < (s + 51 / 50).re := by
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.re_ofNat]
    linarith only [hl]
  have hm : 0 < (-s + 51 / 50).re := by
    norm_num only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.re_ofNat]
    linarith only [hu]
  have h := twoShift_half_hasMellin hp
  have hi := twoShift_half_hasMellin hm
  have hc : MellinConvergent (fun u : ℝ ↦ twoShiftHalfProfile u⁻¹) s := by
    simpa only [Real.rpow_neg_one, Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using
      (MellinConvergent.comp_rpow (f := twoShiftHalfProfile) (s := s) (a := -1)
            (by norm_num only)).mpr
        (by simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using hi.1)
  have he := hasMellin_add h.1 hc
  refine ⟨he.1, ?_⟩
  rw [he.2, mellin_comp_inv, h.2, hi.2]
  rw [twoShift_symmetric_fractions (z := s)
      (by
        rw [sub_eq_neg_add]; exact fun hz ↦ hm.ne' (by rw [hz, Complex.zero_re]))
      (by
        rw [add_comm]; exact fun hz ↦ hp.ne' (by rw [hz, Complex.zero_re]))]
  simp only [sub_eq_neg_add, add_comm s (51 / 50 : ℂ)]
  ring

/-- The translated bilateral profile, scaled by a complex coefficient. Its Mellin
transform acquires the factor exp(b s) for a translation by b on the log axis. -/
noncomputable def twoShiftTranslatedProfile (c : ℂ) (b u : ℝ) : ℂ :=
  let v := Real.exp (-b) * u
  c • (twoShiftHalfProfile v + twoShiftHalfProfile v⁻¹)

private theorem twoShift_translated_hasMellin (c : ℂ) (b : ℝ) {s : ℂ} (hl : -(51 / 50 : ℝ) < s.re)
    (hu : s.re < 51 / 50) :
    HasMellin (twoShiftTranslatedProfile c b) s
      (c * (Complex.exp ((b : ℂ) * s) * twoShiftSymmetricKernel s)) := by
  let f := fun u : ℝ ↦ twoShiftHalfProfile u + twoShiftHalfProfile u⁻¹
  have h : HasMellin f s (twoShiftSymmetricKernel s) := twoShift_symmetric_hasMellin hl hu
  have hc := (MellinConvergent.comp_mul_left (Real.exp_pos (-b))).mpr h.1
  have hm := hasMellin_const_smul hc c
  rw [mellin_comp_mul_left f s (Real.exp_pos _), h.2,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
    Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg, neg_mul_neg] at hm
  exact hm

/-- The four translated profiles have Mellin transform equal to the analytic cosine
kernel throughout its pole-free strip. Each translated summand is integrable there. -/
theorem twoShift_cosine_hasMellin {s : ℂ} (hl : -(51 / 50 : ℝ) < s.re) (hu : s.re < 51 / 50) :
    HasMellin
      (fun u ↦
        twoShiftTranslatedProfile (5 / 4) 0 u + twoShiftTranslatedProfile (-1 / 2) (14 / 5) u +
          twoShiftTranslatedProfile (1 / 2) 3 u +
          twoShiftTranslatedProfile (-1 / 4) (1 / 5) u)
      s (twoShiftCosineKernel s) := by
  have h :=
    twoShift_mellin_add
      (twoShift_mellin_add
        (twoShift_mellin_add (twoShift_translated_hasMellin (5 / 4) 0 hl hu)
          (twoShift_translated_hasMellin (-1 / 2) (14 / 5) hl hu))
        (twoShift_translated_hasMellin (1 / 2) 3 hl hu))
      (twoShift_translated_hasMellin (-1 / 4) (1 / 5) hl hu)
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [twoShiftCosineKernel, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  ring

/-- The symmetric Mellin kernel is absolutely integrable on the imaginary axis.
Its values there are the norms of the original sixth-pole kernel. -/
theorem twoShift_symmetric_vertical : Complex.VerticalIntegrable twoShiftSymmetricKernel 0 := by
  have h :=
    quarterKernel570.mellin_integrable 0 1 (by norm_num only)
      (by linarith only [quarterKernel570.delta_pos]) zero_lt_one
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  unfold Complex.VerticalIntegrable
  apply h.norm.ofReal.congr
  filter_upwards with t
  change
    (‖quarterKernel570.function (Complex.I * t)‖ : ℂ) =
      twoShiftSymmetricKernel (((0 : ℝ) : ℂ) + t * Complex.I)
  rw [Complex.ofReal_zero, zero_add, mul_comm (t : ℂ) Complex.I, twoShift_symmetric_axis,
    quarter_zero_norm_570]

/-- The continuous log-coordinate representative of the symmetric profile, with
the single value 3/16 at u = 1. Its exponential decay and quadratic factor
are shared by the original and reflected halves. -/
noncomputable def twoShiftSymmetricProfile (u : ℝ) : ℝ :=
  let v := |Real.log u|
  Real.exp (-(51 / 50) * v) * (3 / 16 + (3 * (51 / 50) / 16) * v + ((51 / 50) ^ 2 / 16) * v ^ 2)

private theorem twoShift_half_below {u : ℝ} (hu : 0 < u) (h1 : u ≤ 1) :
    twoShiftHalfProfile u = (twoShiftSymmetricProfile u : ℂ) := by
  have hi : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu, h1⟩
  have he : (u : ℂ) ^ (51 / 50 : ℂ) = (Real.exp (Real.log u * (51 / 50)) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
      Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_ofNat]
  simp only [twoShiftHalfProfile, Analysis.logPowerWeight_eq_smul, Analysis.mellinWeightZero,
    Set.indicator_of_mem hi, Complex.real_smul, smul_eq_mul, mul_one, he, twoShiftSymmetricProfile,
    abs_of_nonpos (Real.log_nonpos hu.le h1)]
  rw [show -(51 / 50 : ℝ) * -Real.log u = Real.log u * (51 / 50) by ring]
  push_cast
  ring

private theorem twoShift_half_above {u : ℝ} (hu : 1 < u) : twoShiftHalfProfile u = 0 := by
  have hi : u ∉ Set.Ioc (0 : ℝ) 1 := fun h ↦ hu.not_ge h.2
  simp only [twoShiftHalfProfile, Analysis.logPowerWeight_eq_smul, Analysis.mellinWeightZero,
    Set.indicator_of_notMem hi, smul_zero, add_zero]

/-- Away from the join, the two half-profiles sum to the continuous representative.
At positive inputs inversion of the argument merely negates the logarithm. -/
theorem twoShift_profile_eq_off_one {u : ℝ} (hu : 0 < u) (h1 : u ≠ 1) :
    twoShiftHalfProfile u + twoShiftHalfProfile u⁻¹ = (twoShiftSymmetricProfile u : ℂ) := by
  rcases lt_or_gt_of_ne h1 with hl | hr
  · rw [twoShift_half_below hu hl.le, twoShift_half_above ((one_lt_inv₀ hu).mpr hl), add_zero]
  · rw [twoShift_half_above hr, zero_add,
      twoShift_half_below (inv_pos.mpr hu) ((inv_lt_one₀ hu).mpr hr).le]
    simp only [twoShiftSymmetricProfile, Real.log_inv, abs_neg]

/-- Changing the join value to 3/16 leaves the forward Mellin transform unchanged
throughout the open pole-free strip. -/
theorem twoShift_profile_hasMellin {s : ℂ} (hl : -(51 / 50 : ℝ) < s.re) (hu : s.re < 51 / 50) :
    HasMellin (fun u ↦ (twoShiftSymmetricProfile u : ℂ)) s (twoShiftSymmetricKernel s) := by
  have h := twoShift_symmetric_hasMellin hl hu
  have he :
    (fun u : ℝ ↦
        (u : ℂ) ^ (s - 1) •
          (twoShiftHalfProfile u +
            twoShiftHalfProfile u⁻¹)) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • (twoShiftSymmetricProfile u : ℂ)) := by
    filter_upwards [MeasureTheory.Measure.ae_ne _ (1 : ℝ),
      MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u h1 hu0
    rw [twoShift_profile_eq_off_one hu0 h1]
  exact ⟨h.1.congr he, (MeasureTheory.integral_congr_ae he.symm).trans h.2⟩

/-- On the entire positive axis the inverse Mellin transform of the symmetric kernel
equals its exponential quadratic profile, including the join at one. -/
theorem twoShift_profile_inversion {u : ℝ} (hu : 0 < u) :
    mellinInv 0 twoShiftSymmetricKernel u = (twoShiftSymmetricProfile u : ℂ) := by
  let f := fun v : ℝ ↦ (twoShiftSymmetricProfile v : ℂ)
  have h (t : ℝ) :
    HasMellin f (((0 : ℝ) : ℂ) + t * Complex.I)
      (twoShiftSymmetricKernel (((0 : ℝ) : ℂ) + t * Complex.I)) := by
    apply twoShift_profile_hasMellin <;>
      norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hv : Complex.VerticalIntegrable (mellin f) 0 :=
    twoShift_symmetric_vertical.congr (Filter.Eventually.of_forall fun t ↦ (h t).2.symm)
  have h0 : MellinConvergent f ((0 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (h 0).1
  have hc : ContinuousAt f u := by
    dsimp only [f, twoShiftSymmetricProfile]
    fun_prop (disch := exact hu.ne')
  change mellinInv 0 twoShiftSymmetricKernel u = f u
  rw [← mellinInv_mellin_eq 0 f hu h0 hv hc]
  unfold mellinInv
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦
        congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-(((0 : ℝ) : ℂ) + t * Complex.I)) • z) (h t).2.symm)

/-- Each exponential translate of the symmetric kernel inverts to the same continuous
profile at the rescaled argument. This includes all four joining points of the cosine test. -/
theorem twoShift_shift_inversion (b : ℝ) {u : ℝ} (hu : 0 < u) :
    Analysis.inverseMellin (fun s : ℂ ↦ Complex.exp ((b : ℂ) * s) * twoShiftSymmetricKernel s) 0 u =
      (twoShiftSymmetricProfile (u * Real.exp (-b)) : ℂ) := by
  rw [Analysis.inverseMellin_exp_mul twoShiftSymmetricKernel b 0 hu,
    Analysis.inverseMellin_eq_mellinInv, twoShift_profile_inversion (mul_pos hu (Real.exp_pos _))]

private theorem twoShift_shift_integrable (b : ℝ) {u : ℝ} (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Complex.exp ((b : ℂ) * (Complex.I * t)) * twoShiftSymmetricKernel (Complex.I * t) *
          (u : ℂ) ^ (-(Complex.I * t))) := by
  let g := fun t : ℝ ↦ Complex.exp ((b : ℂ) * (Complex.I * t)) * (u : ℂ) ^ (-(Complex.I * t))
  have hc : Continuous g := by
    unfold g
    fun_prop (disch := exact Complex.ofReal_ne_zero.mpr hu.ne')
  have hg (t : ℝ) : ‖g t‖ ≤ 1 := by
    simp only [g, norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hu,
      Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_mul, sub_zero, neg_zero, Real.rpow_zero, Real.exp_zero,
      mul_one, le_refl]
  have hi : MeasureTheory.Integrable (fun t : ℝ ↦ twoShiftSymmetricKernel (Complex.I * t)) := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_zero, zero_add, mul_comm Complex.I] using
      twoShift_symmetric_vertical
  exact
    (hi.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hg)).congr
      (Filter.Eventually.of_forall fun t ↦ by
        dsimp only [g]; ring)

/-- On the positive axis, including all joining points, the cosine kernel inverts to
the four continuous exponential-quadratic profiles with the phase-estimate coefficients. -/
theorem twoShift_cosine_inversion {u : ℝ} (hu : 0 < u) :
    Analysis.inverseMellin twoShiftCosineKernel 0 u =
      ((5 / 4 * twoShiftSymmetricProfile u -
                1 / 2 * twoShiftSymmetricProfile (u * Real.exp (-(14 / 5))) +
              1 / 2 * twoShiftSymmetricProfile (u * Real.exp (-3)) -
            1 / 4 * twoShiftSymmetricProfile (u * Real.exp (-(1 / 5))) :
          ℝ) :
        ℂ) := by
  let F := fun (b t : ℝ) ↦
    Complex.exp ((b : ℂ) * (Complex.I * t)) * twoShiftSymmetricKernel (Complex.I * t) *
      (u : ℂ) ^ (-(Complex.I * t))
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hv (b : ℝ) : d * (∫ t : ℝ, F b t) = (twoShiftSymmetricProfile (u * Real.exp (-b)) : ℂ) := by
    simpa only [Analysis.inverseMellin, Complex.ofReal_zero, zero_add, F, d] using
      twoShift_shift_inversion b hu
  have hf (b : ℝ) : MeasureTheory.Integrable (F b) := twoShift_shift_integrable b hu
  have ht (t : ℝ) :
    twoShiftCosineKernel (Complex.I * t) * (u : ℂ) ^ (-(Complex.I * t)) =
      (5 / 4 : ℂ) * F 0 t - (1 / 2 : ℂ) * F (14 / 5) t + (1 / 2 : ℂ) * F 3 t -
        (1 / 4 : ℂ) * F (1 / 5) t := by
    simp only [twoShiftCosineKernel, F, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    ring
  simp only [Analysis.inverseMellin, Complex.ofReal_zero, zero_add, ht]
  have hA := (hf 0).const_mul (5 / 4 : ℂ)
  have hB := (hf (14 / 5)).const_mul (1 / 2 : ℂ)
  have hC := (hf 3).const_mul (1 / 2 : ℂ)
  have hD := (hf (1 / 5)).const_mul (1 / 4 : ℂ)
  have hab := hA.sub hB
  have habc := hab.add hC
  change MeasureTheory.Integrable (fun t ↦ 5 / 4 * F 0 t - 1 / 2 * F (14 / 5) t) at hab
  change
    MeasureTheory.Integrable (fun t ↦ 5 / 4 * F 0 t - 1 / 2 * F (14 / 5) t + 1 / 2 * F 3 t) at habc
  rw [MeasureTheory.integral_sub habc hD, MeasureTheory.integral_add hab hC,
    MeasureTheory.integral_sub hA hB]
  simp only [MeasureTheory.integral_const_mul]
  have h0 := hv 0
  simp only [neg_zero, Real.exp_zero, mul_one] at h0
  dsimp only [d] at h0 hv
  push_cast at h0 hv ⊢
  linear_combination
    (5 / 4 : ℂ) * h0 - (1 / 2 : ℂ) * hv (14 / 5) + (1 / 2 : ℂ) * hv 3 - (1 / 4 : ℂ) * hv (1 / 5)

private noncomputable def twoShiftProfilePair (s v : ℝ) : ℝ :=
  twoShiftSymmetricProfile (Real.exp v * Real.exp (-s)) +
    twoShiftSymmetricProfile (Real.exp (-v) * Real.exp (-s))

private theorem twoShift_profile_pair_eq {s v : ℝ} (hs : 0 ≤ s) (hv : s ≤ v) :
    let a := (51 / 50 : ℝ)
    let P := fun t : ℝ ↦ 3 / 8 + 3 * a / 8 * t + a ^ 2 / 8 * t ^ 2
    twoShiftProfilePair s v =
      Real.exp (-a * v) * ((Real.exp (-a * s) * P (v + s) + Real.exp (a * s) * P (v - s)) / 2) := by
  intro a P
  unfold twoShiftProfilePair twoShiftSymmetricProfile
  rw [← Real.exp_add, ← Real.exp_add, Real.log_exp, Real.log_exp,
    abs_of_nonneg (by linarith only [hv] : 0 ≤ v + -s),
    abs_of_nonpos (by linarith only [hs, hv] : -v + -s ≤ 0)]
  dsimp only
  rw [show -(51 / 50 : ℝ) * (v + -s) = -a * v + a * s by
      dsimp only [a]; ring,
    show -(51 / 50 : ℝ) * -(-v + -s) = -a * v + -a * s by
      dsimp only [a]; ring,
    Real.exp_add, Real.exp_add]
  dsimp only [P, a]
  ring

/-- For log arguments at least three, adding the forward and reflected profile
corrections gives exactly the polynomial weight in the certified common Euler tail. -/
theorem twoShift_profile_euler_eq {v : ℝ} (hv : 3 ≤ v) :
    let D := fun s : ℝ ↦
      twoShiftSymmetricProfile (Real.exp v * Real.exp (-s)) +
        twoShiftSymmetricProfile (Real.exp (-v) * Real.exp (-s))
    (D 3 - D (14 / 5)) / 2 + (D 0 - D (1 / 5)) / 4 =
      Real.exp (-(51 / 50) * v) * twoShiftEulerPoly v := by
  change
    (twoShiftProfilePair 3 v - twoShiftProfilePair (14 / 5) v) / 2 +
        (twoShiftProfilePair 0 v - twoShiftProfilePair (1 / 5) v) / 4 =
      _
  rw [twoShift_profile_pair_eq (by norm_num only) hv,
    twoShift_profile_pair_eq (by norm_num only) (by linarith only [hv] : 14 / 5 ≤ v),
    twoShift_profile_pair_eq (le_refl 0) (by linarith only [hv] : 0 ≤ v),
    twoShift_profile_pair_eq (by norm_num only) (by linarith only [hv] : 1 / 5 ≤ v)]
  rw [twoShiftEulerPoly_eq_shifts]
  simp only [mul_zero, Real.exp_zero, one_mul, add_zero, sub_zero]
  ring

/-- At reciprocal arguments exp(v) and exp(-v) with v at least three, subtracting
the unmodulated inverse from the cosine inverse gives the certified Euler weight
after summing the two directions. -/
theorem twoShift_inverse_euler_eq {v : ℝ} (hv : 3 ≤ v) :
    let D := fun u : ℝ ↦
      (Analysis.inverseMellin twoShiftCosineKernel 0 u).re - twoShiftSymmetricProfile u
    D (Real.exp v) + D (Real.exp (-v)) = Real.exp (-(51 / 50) * v) * twoShiftEulerPoly v := by
  intro D
  have he := twoShift_profile_euler_eq hv
  dsimp only at he
  simp only [neg_zero, Real.exp_zero, mul_one] at he
  simp only [D, twoShift_cosine_inversion (Real.exp_pos _), Complex.ofReal_re]
  linarith only [he]

/-- For each positive integer with logarithm at least three, the paired contour
correction times the von Mangoldt weight is precisely the summand of the common
Euler tail at exponent 38/25. -/
theorem twoShift_inverse_euler_term {n : ℕ} (hn : 0 < n) (hl : 3 ≤ Real.log n) :
    let D := fun u : ℝ ↦
      (Analysis.inverseMellin twoShiftCosineKernel 0 u).re - twoShiftSymmetricProfile u
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * (D n + D (n : ℝ)⁻¹) =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
        twoShiftEulerPoly (Real.log n) := by
  intro D
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h := twoShift_inverse_euler_eq hl
  change D (Real.exp (Real.log n)) + D (Real.exp (-Real.log n)) = _ at h
  rw [Real.exp_neg, Real.exp_log hp] at h
  have hd : (n : ℝ) ^ (38 / 25 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (51 / 50 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num only
  rw [h, mul_comm (-(51 / 50)) (Real.log n), ← Real.rpow_def_of_pos hp, Real.rpow_neg hp.le,
    Real.sqrt_eq_rpow, hd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- At cutoffs at least 85264 the paired inverse-transform correction equals the signed Euler
tail with exponent 38/25, retaining the common trace deficit for the phase estimate. -/
theorem twoShift_inverse_tail_eq {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ} (hX : 85264 ≤ X) :
    let D := fun u : ℝ ↦
      (Analysis.inverseMellin twoShiftCosineKernel 0 u).re - twoShiftSymmetricProfile u
    (∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val * (D k.val + D (k.val : ℝ)⁻¹))) =
      ∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / (k.val : ℝ) ^ (38 / 25 : ℝ) *
            twoShiftEulerPoly (Real.log k.val)) := by
  intro D
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
  have hx : Real.exp 3 ≤ X := by
    rw [show (3 : ℝ) = (3 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, hX]
  have hh (k : { n : ℕ // ⌊X⌋₊ < n }) :=
    twoShift_inverse_euler_term (Nat.zero_le _ |>.trans_lt k.property)
      ((Real.le_log_iff_exp_le (Nat.cast_pos.mpr (Nat.zero_le _ |>.trans_lt k.property))).mpr
        (hx.trans (Nat.lt_of_floor_lt k.property).le))
  simp_rw [show
      ∀ k : { n : ℕ // ⌊X⌋₊ < n },
        ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val * (D k.val + D (k.val : ℝ)⁻¹) = _
      from hh]

/-- Under RH, the signed sum of the actual paired inverse transforms above a cutoff
of at least 85264 costs less than 0.327988 for three characters of trace at least -1.
The pointwise profile identity permits the certified Euler estimate on the entire tail. -/
theorem twoShift_inverse_tail_bound {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ} (hX : 85264 ≤ X)
    (hRH : RiemannHypothesis) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let D := fun u : ℝ ↦
      (Analysis.inverseMellin twoShiftCosineKernel 0 u).re - twoShiftSymmetricProfile u
    (∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val * (D k.val + D (k.val : ℝ)⁻¹))) <
      327988 / 1000000 := by
  intro D
  have h := three_trace_tail_large a b c hX hRH ht
  dsimp only at h
  rw [twoShift_inverse_tail_eq a b c hX]
  linarith only [h]

private theorem twoShift_den_re {z : ℂ} :
    (((51 / 50 : ℂ) - z) * (51 / 50 + z)).re = (51 / 50 : ℝ) ^ 2 - z.re ^ 2 + z.im ^ 2 := by
  rw [mul_comm, ← sq_sub_sq]
  simp only [Complex.sub_re, pow_two, Complex.mul_re, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- On the closed strip of real parts between -3/4 and 3/4 the even sixth-pole
kernel has uniform quadratic decay. The real part of its quadratic denominator
is bounded below by a positive constant plus the squared imaginary part. -/
theorem twoShift_symmetric_decay {z : ℂ} (hl : -(3 / 4 : ℝ) ≤ z.re) (hu : z.re ≤ 3 / 4) :
    ‖twoShiftSymmetricKernel z‖ ≤ 100 / (1 + ‖z‖ ^ 2) := by
  let D := ((51 / 50 : ℂ) - z) * (51 / 50 + z)
  have hr := sq_le_sq' hl hu
  have hd := Complex.re_le_norm D
  change (((51 / 50 : ℂ) - z) * (51 / 50 + z)).re ≤ ‖D‖ at hd
  rw [twoShift_den_re] at hd
  have hpos : 1 / 3 ≤ ‖D‖ := by linarith only [hd, hr, sq_nonneg z.im]
  have hc : (1 / 3 : ℝ) ^ 2 ≤ ‖D‖ ^ 2 := pow_le_pow_left₀ (by norm_num only) hpos 2
  have hc3 := mul_le_mul_of_nonneg_right hc (norm_nonneg D)
  change ‖(51 / 50 : ℂ) ^ 5 / D ^ 3‖ ≤ _
  rw [norm_div, norm_pow, norm_pow, norm_div, Complex.norm_ofNat, Complex.norm_ofNat,
    div_le_div_iff₀ (pow_pos (by linarith only [hpos] : 0 < ‖D‖) _)
      (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _)),
    Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [hd, hr, hc3, sq_nonneg z.im]

/-- Both poles lie outside the closed three-quarter strip, so the rational kernel
is complex differentiable at every point of the strip. -/
theorem twoShift_symmetric_diff {z : ℂ} (hl : -(3 / 4 : ℝ) ≤ z.re) (hu : z.re ≤ 3 / 4) :
    DifferentiableAt ℂ twoShiftSymmetricKernel z := by
  have hn : ((51 / 50 : ℂ) - z) * (51 / 50 + z) ≠ 0 := by
    intro h
    have hh := twoShift_den_re (z := z)
    rw [h, Complex.zero_re] at hh
    nlinarith only [hh, sq_le_sq' hl hu, sq_nonneg z.im]
  unfold twoShiftSymmetricKernel
  fun_prop (disch := exact pow_ne_zero _ hn)

private theorem twoShift_line_re (c t : ℝ) : ((c : ℂ) + Complex.I * t).re = c := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    zero_mul, mul_zero, sub_zero, add_zero]

/-- Uniform Cauchy decay makes the symmetric kernel integrable along each vertical
line with real part between -3/4 and 3/4. -/
theorem twoShift_symmetric_line {c : ℝ} (hl : -(3 / 4 : ℝ) ≤ c) (hu : c ≤ 3 / 4) :
    MeasureTheory.Integrable (fun t : ℝ ↦ twoShiftSymmetricKernel ((c : ℂ) + Complex.I * t)) := by
  have hc : Continuous (fun t : ℝ ↦ twoShiftSymmetricKernel ((c : ℂ) + Complex.I * t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply
      (twoShift_symmetric_diff (by rwa [twoShift_line_re])
          (by rwa [twoShift_line_re])).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul (100 : ℝ)).mono' hc.aestronglyMeasurable
  filter_upwards with t
  have hd :=
    twoShift_symmetric_decay (z := (c : ℂ) + Complex.I * t) (by rwa [twoShift_line_re])
      (by rwa [twoShift_line_re])
  apply hd.trans
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by norm_num only) (by positivity)
  rw [Complex.sq_norm, Complex.normSq_apply, twoShift_line_re]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add]
  nlinarith only [sq_nonneg c]

/-- The continuous exponential quadratic is the inverse on every line in the closed
three-quarter strip. Hence the inverse is independent of the line used for the contour. -/
theorem twoShift_symmetric_line_inversion {c u : ℝ} (hl : -(3 / 4 : ℝ) ≤ c) (hu : c ≤ 3 / 4)
    (hx : 0 < u) :
    Analysis.inverseMellin twoShiftSymmetricKernel c u = (twoShiftSymmetricProfile u : ℂ) := by
  let f := fun v : ℝ ↦ (twoShiftSymmetricProfile v : ℂ)
  have h (t : ℝ) :
    HasMellin f ((c : ℂ) + t * Complex.I) (twoShiftSymmetricKernel ((c : ℂ) + t * Complex.I)) := by
    apply twoShift_profile_hasMellin <;> rw [mul_comm (t : ℂ) Complex.I, twoShift_line_re] <;>
      linarith only [hl, hu]
  have hv : Complex.VerticalIntegrable twoShiftSymmetricKernel c := by
    simpa only [Complex.VerticalIntegrable, mul_comm Complex.I] using twoShift_symmetric_line hl hu
  have hi := hv.congr (Filter.Eventually.of_forall fun t ↦ (h t).2.symm)
  have h0 : MellinConvergent f (c : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (h 0).1
  have hc : ContinuousAt f u := by
    dsimp only [f, twoShiftSymmetricProfile]
    fun_prop (disch := exact hx.ne')
  change Analysis.inverseMellin twoShiftSymmetricKernel c u = f u
  rw [Analysis.inverseMellin_eq_mellinInv, ← mellinInv_mellin_eq c f hx h0 hi hc]
  unfold mellinInv
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦
        congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) • z) (h t).2.symm)

/-- The symmetric sixth-pole test as an admissible Mellin kernel for the character
and principal contour formulas. Its inverse is the positive exponential quadratic,
and the strip of width 1/8 fits inside the region of uniform decay. -/
@[expose]
noncomputable def twoShiftSymmetricMellin : LLS.PaperStatements.MellinKernel where
  function := twoShiftSymmetricKernel
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {z | z.re ∈ Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)}
  region_open := isOpen_Ioo.preimage Complex.continuous_re
  strip_subset := by
    intro z hz
    change -1 / 2 - 1 / 8 < z.re ∧ z.re ≤ 1 / 2 + 1 / 8 at hz
    exact ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
  holomorphic := fun z hz ↦ (twoShift_symmetric_diff hz.1.1.le hz.1.2.le).differentiableWithinAt
  regularized := fun z ↦ (z + 1 / 2) * twoShiftSymmetricKernel z
  regularized_holomorphic := fun z hz ↦
    (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const _).mul
        (twoShift_symmetric_diff hz.1.le hz.2.le)).differentiableWithinAt
  regularized_eq := fun _ _ _ ↦ rfl
  decay := fun _ _ ↦ ⟨100, by norm_num only, fun _ hz _ ↦ twoShift_symmetric_decay hz.1.le hz.2.le⟩
  mellin_integrable := fun _ _ hl hu hx ↦
    LLS.PaperStatements.integrable_inverseMellin_of_line hx
      (twoShift_symmetric_line (by linarith only [hl]) (by linarith only [hu]))
  mellin_eq := by
    intro c u hl hu hx
    rw [twoShift_symmetric_line_inversion (by linarith only [hl]) (by linarith only [hu]) hx,
      twoShift_symmetric_line_inversion (by norm_num only) (by norm_num only) hx]
  mellin_nonneg := by
    intro u hx
    rw [twoShift_symmetric_line_inversion (by norm_num only) (by norm_num only) hx,
      Complex.ofReal_re]
    unfold twoShiftSymmetricProfile
    positivity
  mellin_nonzero := by
    refine ⟨1, zero_lt_one, ?_⟩
    rw [twoShift_symmetric_line_inversion (by norm_num only) (by norm_num only) zero_lt_one,
      Complex.ofReal_re]
    norm_num only [twoShiftSymmetricProfile, Real.log_one, abs_zero, mul_zero, Real.exp_zero,
      zero_pow, OfNat.ofNat_ne_zero, add_zero, one_mul]
  mellin_real := by
    intro u hx
    rw [twoShift_symmetric_line_inversion (by norm_num only) (by norm_num only) hx,
      Complex.ofReal_im]

/-- At a nonnegative frequency the real symmetric-kernel zero sum equals the two
vertical integrals less the forward arithmetic sum. The regularization residue
vanishes because the symmetric kernel is holomorphic at minus one half. -/
theorem twoShift_symmetric_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let W := fun s : ℂ ↦ twoShiftSymmetricKernel s * (x : ℂ) ^ s
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' ρ, twoShiftSymmetricMellin.oscillatingZeroTerm χ x ρ).re =
      (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re +
          (d * ∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)).re -
        (∑' n, twoShiftSymmetricMellin.summand χ x n).re := by
  intro x W l r d
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula
      twoShiftSymmetricMellin hq hG hp hn (inv_ne_one.mpr hn) (a := (-9 / 16 : ℝ)) (b := 9 / 16)
      (by norm_num only)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (Real.one_le_exp hb) (by norm_num only)
      (by norm_num only)
  have hz (F : ℂ → ℂ) : twoShiftSymmetricMellin.weightedResidue F x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv F (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    (∑' n, twoShiftSymmetricMellin.summand χ x n) =
      twoShiftSymmetricMellin.weightedResidue _ x (-1 / 2) -
          (∑' ρ, twoShiftSymmetricMellin.oscillatingZeroTerm χ x ρ) +
        d * (∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)) +
        d * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)) at h
  rw [hz, zero_sub] at h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.neg_re] at he
  linarith only [he]

private theorem twoShift_symmetric_zero_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ)
    (ρ : ℂ) :
    (twoShiftSymmetricMellin.oscillatingZeroTerm χ (Real.exp b) ρ).re =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ((51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + ρ.im ^ 2) ^ 3) *
        Real.cos (b * ρ.im) := by
  unfold LLS.PaperStatements.MellinKernel.oscillatingZeroTerm
    LLS.PaperStatements.MellinKernel.kernelZeroTerm
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
    Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  change
    (((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℤ) : ℂ) *
          twoShiftSymmetricKernel (Complex.I * ρ.im) *
          _).re =
      _
  rw [twoShift_symmetric_axis, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, twoShift_exp_axis]

/-- Under GRH the fixed cosine mass is exactly the combination of the four real
zero sums covered by the admissible symmetric-kernel contour formula. -/
theorem twoShift_mass_four_contours {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1) :
    let Z := fun b : ℝ ↦ (∑' ρ, twoShiftSymmetricMellin.oscillatingZeroTerm χ (Real.exp b) ρ).re
    twoShiftCosineMass χ = 5 / 4 * Z 0 - 1 / 2 * Z (14 / 5) + 1 / 2 * Z 3 - 1 / 4 * Z (1 / 5) := by
  intro Z
  let f := fun (b : ℝ) (ρ : ℂ) ↦ (twoShiftSymmetricMellin.oscillatingZeroTerm χ (Real.exp b) ρ).re
  have hs (b : ℝ) :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm twoShiftSymmetricMellin hq hG hp
      hn (inv_ne_one.mpr hn) (Real.exp_pos b)
  have hf (b : ℝ) : Summable (f b) :=
    (hs b).norm.of_norm_bounded
      (fun ρ ↦ by
        simpa only [f, Real.norm_eq_abs] using
          Complex.abs_re_le_norm (twoShiftSymmetricMellin.oscillatingZeroTerm χ (Real.exp b) ρ))
  have hZ (b : ℝ) : Z b = ∑' ρ, f b ρ := Complex.re_tsum (hs b)
  have hA := (hf 0).mul_left (5 / 4)
  have hB := (hf (14 / 5)).mul_left (1 / 2)
  have hC := (hf 3).mul_left (1 / 2)
  have hD := (hf (1 / 5)).mul_left (1 / 4)
  simp only [hZ, ← tsum_mul_left]
  rw [← hA.tsum_sub hB, ← (hA.sub hB).tsum_add hC, ← ((hA.sub hB).add hC).tsum_sub hD]
  apply tsum_congr
  intro ρ
  simp only [f, twoShift_symmetric_zero_re, twoShiftCosineWeight, zero_mul, Real.cos_zero, mul_one]
  ring

/-- The contour expression for a single frequency: the completed left integral
and the right gamma integral, less the forward symmetric-profile arithmetic sum. -/
noncomputable def twoShiftContourValue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let x := Real.exp b
  let W := fun s : ℂ ↦ twoShiftSymmetricKernel s * (x : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re +
      (d * ∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)).re -
    (∑' n, twoShiftSymmetricMellin.summand χ x n).re

/-- Under GRH the fixed-frequency cosine mass of a primitive nonprincipal character
equals four explicit contour and arithmetic expressions with no remaining character zero sum. -/
theorem twoShift_mass_eq_contours {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1) :
    twoShiftCosineMass χ =
      5 / 4 * twoShiftContourValue χ 0 - 1 / 2 * twoShiftContourValue χ (14 / 5) +
          1 / 2 * twoShiftContourValue χ 3 -
        1 / 4 * twoShiftContourValue χ (1 / 5) := by
  have h (b : ℝ) (hb : 0 ≤ b) :
    (∑' ρ, twoShiftSymmetricMellin.oscillatingZeroTerm χ (Real.exp b) ρ).re =
      twoShiftContourValue χ b :=
    twoShift_symmetric_contour hq hG hp hn hb
  have hm := twoShift_mass_four_contours hq hG hp hn
  dsimp only at hm
  simpa only [h 0 (le_refl _), h (14 / 5) (by norm_num only), h 3 (by norm_num only),
    h (1 / 5) (by norm_num only)] using hm

/-- For the Jacobi character of a prime pair in a squarefree integer, the original
cosine budget reduces to the main-scale contour and the four symmetric-kernel contours. -/
theorem pair_twoShift_contour_budget {n p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] [Fact q.Prime]
    (hs : Squarefree n) (hd : p * q ∣ n) (ho : Odd (p * q))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hx : 0 < X) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) ho
    twoShiftCosineBudget χ X =
      contourNonEuler570 χ X - reflectedIntegral570 χ X +
        (5 / 4 * twoShiftContourValue χ 0 - 1 / 2 * twoShiftContourValue χ (14 / 5) +
            1 / 2 * twoShiftContourValue χ 3 -
          1 / 4 * twoShiftContourValue χ (1 / 5)) := by
  intro χ
  have hm :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  rw [pair_twoShift_cosine_budget hs hd ho hG hx,
    twoShift_mass_eq_contours hm hG (pair_character_primitive hs hd ho)
      (pair_character_ne_one hs hd ho hm)]

/-- At each nonnegative frequency the symmetric zeta zero sum is the normalized
left xi integral minus the right xi integral. This uses the same lines and kernel
as the character contour, and the regularization residue is zero. -/
theorem twoShift_symmetric_xi_contour (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 ≤ b) :
    let x := Real.exp b
    let F := fun s : ℂ ↦
      -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
        (twoShiftSymmetricKernel s * (x : ℂ) ^ s)
    (∑' ρ, twoShiftSymmetricMellin.zetaOscillatingZeroTerm x ρ) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro x F
  have h :=
    LLS.PaperStatements.MellinKernel.xiContourIdentity twoShiftSymmetricMellin hRH (a :=
      (-9 / 16 : ℝ)) (b := 9 / 16)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (Real.one_le_exp hb)
  have hz (G : ℂ → ℂ) : twoShiftSymmetricMellin.weightedResidue G x (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv G (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  change
    Complex.I *
        ((∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) -
          ∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)) =
      (2 * Real.pi * Complex.I) *
        (twoShiftSymmetricMellin.weightedResidue _ x (-1 / 2) -
          ∑' ρ, twoShiftSymmetricMellin.zetaOscillatingZeroTerm x ρ) at h
  rw [hz, zero_sub, mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div]
  simp only [mul_comm Complex.I]
  rw [eq_inv_mul_iff_mul_eq₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  linear_combination he

/-- The real normalized xi contour difference at frequency b, on the same
left and right lines used for the three pair characters. -/
noncomputable def twoShiftXiContourValue (b : ℝ) : ℝ :=
  let F := fun s : ℂ ↦
    -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) *
      (twoShiftSymmetricKernel s * ((Real.exp b : ℝ) : ℂ) ^ s)
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
        ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t))).re

/-- Subtracting the unshifted zeta mass leaves the four xi contours with constant
coefficient 1/4. These are the principal terms to subtract from the character contours. -/
theorem twoShift_zeta_eq_contours (hRH : RiemannHypothesis) :
    twoShiftZetaCosineCorrection =
      1 / 4 * twoShiftXiContourValue 0 - 1 / 2 * twoShiftXiContourValue (14 / 5) +
          1 / 2 * twoShiftXiContourValue 3 -
        1 / 4 * twoShiftXiContourValue (1 / 5) := by
  let f := fun (b : ℝ) (ρ : AnalyticNumberTheory.RiemannXi.Zero) ↦
    (twoShiftSymmetricMellin.zetaOscillatingZeroTerm (Real.exp b) ρ).re
  have hs (b : ℝ) :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm twoShiftSymmetricMellin hRH
      (Real.exp_pos b)
  have hf (b : ℝ) : Summable (f b) :=
    (hs b).norm.of_norm_bounded
      (fun ρ ↦ by
        simpa only [f, Real.norm_eq_abs] using
          Complex.abs_re_le_norm (twoShiftSymmetricMellin.zetaOscillatingZeroTerm (Real.exp b) ρ))
  have hv (b : ℝ) (hb : 0 ≤ b) : twoShiftXiContourValue b = ∑' ρ, f b ρ :=
    (congrArg Complex.re (twoShift_symmetric_xi_contour hRH hb)).symm.trans (Complex.re_tsum (hs b))
  have hA := (hf 0).mul_left (1 / 4)
  have hB := (hf (14 / 5)).mul_left (1 / 2)
  have hC := (hf 3).mul_left (1 / 2)
  have hD := (hf (1 / 5)).mul_left (1 / 4)
  rw [hv 0 (le_refl _), hv (14 / 5) (by norm_num only), hv 3 (by norm_num only),
    hv (1 / 5) (by norm_num only), twoShift_zeta_cosine_kernel]
  simp only [← tsum_mul_left]
  rw [← hA.tsum_sub hB, ← (hA.sub hB).tsum_add hC, ← ((hA.sub hB).add hC).tsum_sub hD]
  apply tsum_congr
  intro ρ
  have he (b : ℝ) :
    f b ρ =
      (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity (ρ : ℂ) : ℝ) *
        ((51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 + (ρ : ℂ).im ^ 2) ^ 3) *
        Real.cos (b * (ρ : ℂ).im) := by
    dsimp only [f, LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm,
      LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
      Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    change ((_ * twoShiftSymmetricKernel (Complex.I * (ρ : ℂ).im)) * _).re = _
    rw [twoShift_symmetric_axis, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, twoShift_exp_axis]
  simp only [he, Complex.sub_re, twoShiftCosineKernel, twoShift_symmetric_axis,
    Complex.re_ofReal_mul, Complex.ofReal_re, Complex.add_re, Complex.one_re, Complex.div_ofNat_re,
    twoShift_exp_axis, zero_mul, Real.cos_zero, mul_one]
  ring

/-- The left character-minus-xi integrals and the two right simple-pole
integrals remaining after cancellation of the common even gamma factor. -/
noncomputable def twoShiftLeftDifference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let W := fun s : ℂ ↦ twoShiftSymmetricKernel s * ((Real.exp b : ℝ) : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d * ∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * W (l t)).re -
    (d * ∫ t : ℝ, -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (l t + 1 / 2) * W (l t)).re -
    (d * ∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * W (r t)).re -
    (d * ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * W (r t)).re

/-- For an even character at any real frequency the right gamma integral cancels
in the character-minus-xi contour difference. The arithmetic contribution is the
principal forward sum less the character forward sum. -/
theorem twoShift_even_contour_difference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) (b : ℝ) :
    twoShiftContourValue χ b - twoShiftXiContourValue b =
      twoShiftLeftDifference χ b +
          (∑' n, twoShiftSymmetricMellin.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
        (∑' n, twoShiftSymmetricMellin.summand χ (Real.exp b) n).re := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have h := twoShift_level_one_forward twoShiftSymmetricMellin rfl (Real.exp_pos b)
  dsimp only at h
  have hk : twoShiftSymmetricMellin.function = twoShiftSymmetricKernel := rfl
  rw [show twoShiftSymmetricMellin.function = twoShiftSymmetricKernel from hk] at h
  unfold twoShiftContourValue twoShiftXiContourValue twoShiftLeftDifference
  dsimp only
  rw [hg, h]
  simp only [mul_sub, mul_add, Complex.sub_re, Complex.add_re]
  ring

/-- On the reflected line, the difference of the completed character and xi
integrands has no gamma term for an even self-inverse primitive character.
The conductor, ordinary logarithmic derivatives and two simple poles remain. -/
theorem twoShift_left_log_difference {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (t : ℝ) :
    let s := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    (-logDeriv χ.completedLFunction (s + 1 / 2)) +
        logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s + 1 / 2) =
      Complex.log q + logDeriv χ.LFunction w - logDeriv riemannZeta w - 1 / w - 1 / (w - 1) := by
  intro s w
  have hr : 1 < w.re := by
    simp only [w, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    norm_num only
  have hw : s + 1 / 2 = 1 - w := by
    dsimp only [s, w]; push_cast; ring
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have hL :=
    AnalyticNumberTheory.DirichletLFunction.L_logDeriv_sub_gamma_of_regular hn
      (AnalyticNumberTheory.DirichletLFunction.completed_ne_zero_of_one_le_re hn hr.le)
      (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ
        (zero_lt_one.trans hr))
      (AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ
          (zero_lt_one.trans hr)).differentiableAt
  have hF := LLS.PaperStatements.triangular18_completed_left_reflection hp hn (inv_ne_one.mpr hn) t
  rw [hi] at hF
  change
    -logDeriv χ.completedLFunction (s + 1 / 2) =
      Complex.log q + logDeriv χ.completedLFunction w at hF
  rw [hF, hw, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub,
    AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hr, hL, hg]
  ring

/-- The single-frequency difference after both gamma cancellations. The reflected
ordinary logarithmic derivatives are evaluated to the right of one, so their
Dirichlet series converge absolutely. -/
noncomputable def twoShiftEvenDifference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    ℝ :=
  let W := fun s : ℂ ↦ twoShiftSymmetricKernel s * ((Real.exp b : ℝ) : ℂ) ^ s
  let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  (d *
            ∫ t : ℝ,
              (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
                  1 / (w t - 1)) *
                W (l t)).re -
        (d * ∫ t : ℝ, (1 / (r t - ((-1 / 2 : ℝ) : ℂ))) * W (r t)).re -
        (d * ∫ t : ℝ, (1 / (r t - ((1 / 2 : ℝ) : ℂ))) * W (r t)).re +
      (∑' n, twoShiftSymmetricMellin.summand (1 : DirichletCharacter ℂ 1) (Real.exp b) n).re -
    (∑' n, twoShiftSymmetricMellin.summand χ (Real.exp b) n).re

/-- For even self-inverse primitive nonprincipal characters, the complete contour
difference at any frequency is the ordinary Euler, conductor and pole expression. -/
theorem twoShift_even_difference_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (b : ℝ) :
    twoShiftContourValue χ b - twoShiftXiContourValue b = twoShiftEvenDifference χ b := by
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line twoShiftSymmetricMellin hp hn
      (inv_ne_one.mpr hn) (c := -9 / 16) (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  have hG :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line twoShiftSymmetricMellin (c := -9 / 16)
      (x := Real.exp b)
      (by
        change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) (Real.exp_pos b)
  let W := fun t : ℝ ↦
    twoShiftSymmetricKernel (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      ((Real.exp b : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
  change MeasureTheory.Integrable (fun t : ℝ ↦ -logDeriv χ.completedLFunction (s t) * W t) at hF
  change
    MeasureTheory.Integrable
      (fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t) * W t) at hG
  have h := MeasureTheory.integral_sub hF hG
  have ht (t : ℝ) := congrArg (fun z : ℂ ↦ z * W t) (twoShift_left_log_difference hp hn hi he t)
  have h' :
    (∫ t : ℝ,
        (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
            1 / (w t - 1)) *
          W t) =
      _ :=
    Eq.trans
      (MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun t ↦ by
          simpa only [s, w, add_mul, neg_mul, sub_neg_eq_add] using (ht t).symm))
      h
  rw [twoShift_even_contour_difference χ he b]
  unfold twoShiftLeftDifference twoShiftEvenDifference
  dsimp only
  rw [h', mul_sub, Complex.sub_re]

/-- The residual cosine mass after the shared zeta correction is removed.
The zero-frequency xi term occurs once because the character mass includes
the unshifted kernel while the zeta correction excludes it. -/
noncomputable def twoShiftComparedMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  twoShiftXiContourValue 0 + 5 / 4 * twoShiftEvenDifference χ 0 -
        1 / 2 * twoShiftEvenDifference χ (14 / 5) +
      1 / 2 * twoShiftEvenDifference χ 3 -
    1 / 4 * twoShiftEvenDifference χ (1 / 5)

/-- For each odd prime pair of a squarefree uniform Korselt integer, the full
cosine mass splits into the common zeta correction and the gamma-free remainder. -/
theorem pair_twoShift_compared_mass {n p q : ℕ} [NeZero p] [NeZero q] [Fact p.Prime] [Fact q.Prime]
    [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (hp : Odd p)
    (hq : Odd q) (hd : p * q ∣ n) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let χ := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    twoShiftCosineMass χ = twoShiftComparedMass χ + twoShiftZetaCosineCorrection := by
  intro χ
  have hm :=
    (Fact.out : p.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hprim := pair_character_primitive hs hd (hp.mul hq)
  have hne := pair_character_ne_one hs hd (hp.mul hq) hm
  have he :=
    twoShift_even_difference_eq hprim hne
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hp hq hk hj hv)
  change ∀ b, twoShiftContourValue χ b - twoShiftXiContourValue b = twoShiftEvenDifference χ b at he
  rw [twoShift_mass_eq_contours hm hG hprim hne, twoShift_zeta_eq_contours hG.riemann]
  unfold twoShiftComparedMass
  linarith only [he 0, he (14 / 5), he 3, he (1 / 5)]

private theorem twoShift_symmetric_neg (z : ℂ) :
    twoShiftSymmetricKernel (-z) = twoShiftSymmetricKernel z := by
  unfold twoShiftSymmetricKernel
  rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm ((51 / 50 : ℂ) + z)]

/-- Reflection interchanges the two lines of real parts ±9/16 and inverts the
scale in the power weight. Evenness preserves the symmetric kernel itself. -/
theorem twoShift_reflect_symmetric_line (H : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, H (-(l t)) * (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t)) =
      ∫ t : ℝ, H (r t) * (twoShiftSymmetricKernel (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t) := by
  intro l r
  let F := fun t : ℝ ↦ H (r t) * (twoShiftSymmetricKernel (r t) * ((x⁻¹ : ℝ) : ℂ) ^ r t)
  have hr (t : ℝ) : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  have he (t : ℝ) : H (-(l t)) * (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t) = F (-t) := by
    simp only [F, hr, twoShift_symmetric_neg, Complex.ofReal_inv, Complex.cpow_neg,
      Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- The reflected ordinary logarithmic derivative for the symmetric kernel has
the exact forward arithmetic sum at reciprocal scale, with its minus sign. -/
theorem twoShift_reflected_prime_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (-(l t) + 1 / 2) *
            (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t)) =
      ∑' n, twoShiftSymmetricMellin.summand χ x⁻¹ n := by
  intro l
  have h := twoShift_reflect_symmetric_line (fun s ↦ -logDeriv χ.LFunction (s + 1 / 2)) hx
  dsimp only at h
  dsimp only [l]
  rw [h]
  exact
    (LLS.PaperStatements.MellinKernel.tsum_summand_eq_integral_logDeriv twoShiftSymmetricMellin χ
        (inv_pos.mpr hx) (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)).symm

/-- The constant logarithmic conductor integrates on the left line to the
continuous symmetric profile at the reciprocal scale. -/
theorem twoShift_left_conductor (q : ℕ) {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.log q * (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t)) =
      Complex.log q * (twoShiftSymmetricProfile x⁻¹ : ℂ) := by
  intro l
  have h :=
    twoShift_symmetric_line_inversion (c := -9 / 16) (by norm_num only) (by norm_num only)
      (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  rw [MeasureTheory.integral_const_mul, mul_left_comm, ← h]

/-- The real symmetric arithmetic summand at any positive scale, also at n = 0
where the von Mangoldt factor vanishes. -/
theorem twoShift_symmetric_summand {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    (twoShiftSymmetricMellin.summand χ x n).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n / x)) := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, Complex.zero_re,
      ArithmeticFunction.map_zero, zero_div, zero_mul, mul_zero]
  · have hy := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
    have ht : twoShiftSymmetricMellin.transform (n / x) = (twoShiftSymmetricProfile (n / x) : ℂ) :=
      twoShift_symmetric_line_inversion (c := 0) (by norm_num only) (by norm_num only) hy
    rw [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, ht, mul_comm _ (χ n)]
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.mul_re]
    simp only [Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero]

/-- The real reflected logarithmic derivative is the von Mangoldt series at
reciprocal scale. Its profile argument is n times the original scale. -/
theorem twoShift_reflected_euler_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.LFunction (-(l t) + 1 / 2) *
              (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t))).re =
      ∑' n : ℕ,
        (χ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n * x)) := by
  intro l
  rw [twoShift_reflected_prime_sum χ hx,
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_summand twoShiftSymmetricMellin χ
        (inv_pos.mpr hx))]
  apply tsum_congr
  intro n
  simpa only [div_inv_eq_mul] using (twoShift_symmetric_summand χ (inv_pos.mpr hx) n)

/-- Absolute integrability on the reflected line permits subtraction of the
character and zeta logarithmic derivatives before taking real parts. -/
theorem twoShift_reflected_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (-(l t) + 1 / 2) *
          (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t)) := by
  intro l
  let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_arithmeticMellin_logDeriv twoShiftSymmetricMellin χ
      (inv_pos.mpr hx) (c := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  apply h.comp_neg.congr
  apply Filter.Eventually.of_forall
  intro t
  change
    -logDeriv χ.LFunction (r (-t) + 1 / 2) *
        (twoShiftSymmetricKernel (r (-t)) * ((x⁻¹ : ℝ) : ℂ) ^ r (-t)) =
      _
  have hr : r (-t) = -(l t) := by
    dsimp only [r, l]
    push_cast
    ring
  simp only [hr, twoShift_symmetric_neg, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv]

/-- The reflected difference of ordinary logarithmic derivatives contributes
the principal Euler series minus the character Euler series. -/
theorem twoShift_reflected_euler_difference {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (-(l t) + 1 / 2) * (twoShiftSymmetricKernel (l t) * (x : ℂ) ^ l t)
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n * x))
    let ψ := (1 : DirichletCharacter ℂ 1)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, A ψ t - A χ t)).re = S ψ - S χ := by
  intro l A S ψ
  rw [MeasureTheory.integral_sub (twoShift_reflected_integrable ψ hx)
      (twoShift_reflected_integrable χ hx),
    mul_sub, Complex.sub_re]
  exact
    congrArg₂ (· - ·) (twoShift_reflected_euler_series ψ hx) (twoShift_reflected_euler_series χ hx)

/-- The normalized symmetric-kernel integral on the line of real part c with a
simple pole at p and positive scale x. -/
noncomputable def twoShiftSymmetricPole (c p x : ℝ) : ℂ :=
  let s := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, (1 / (s t - (p : ℂ))) * (twoShiftSymmetricKernel (s t) * (x : ℂ) ^ s t)

/-- Across the two comparison lines each interior real pole contributes the
value of the symmetric weight at that pole. -/
theorem twoShift_symmetric_pole_difference {x p : ℝ} (hx : 1 ≤ x) (hlP : -9 / 16 < p)
    (huP : p < 9 / 16) :
    twoShiftSymmetricPole (9 / 16) p x - twoShiftSymmetricPole (-9 / 16) p x =
      twoShiftSymmetricKernel (p : ℂ) * (x : ℂ) ^ (p : ℂ) := by
  let a : ℝ := -9 / 16
  let b : ℝ := 9 / 16
  let K := twoShiftSymmetricMellin
  let F := fun s : ℂ ↦ (1 / (s - (p : ℂ))) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hd : K.delta = 1 / 8 := rfl
  have hl : -1 / 2 - K.delta < a := by
    rw [hd]; norm_num only [a]
  have hu : b ≤ 1 / 2 + K.delta := by
    rw [hd]; norm_num only [b]
  have ha : a ≤ b := by norm_num only [a, b]
  have hxp := zero_lt_one.trans_le hx
  have hi0 :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K (hl.trans_le ha) hu
      (by norm_num only [b]) (ne_of_gt huP) hxp
  have hia :=
    LLS.PaperStatements.MellinKernel.integrable_pole_power_line K hl (ha.trans hu)
      (by norm_num only [a, b]) (ne_of_lt hlP) hxp
  have ht := LLS.PaperStatements.MellinKernel.tendsto_pole_horizontalIntegral K ha hl hu hx p
  have hlim :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K := F) (a := a) (b := b) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          ht (-1) (Or.inr rfl))
      (by simpa only [F, T, one_mul] using ht 1 (Or.inl rfl))
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hia)
      (by simpa only [F, mul_comm Complex.I, mul_assoc] using hi0)
  let H := fun z : ℂ ↦ K.function z * (x : ℂ) ^ z
  have hH (z : ℂ) (hr : a ≤ z.re) (hs : z.re ≤ b) : AnalyticAt ℂ H z := by
    have hd := twoShift_den_re (z := z)
    have hlz : -(3 / 4 : ℝ) ≤ z.re := le_trans (by norm_num only [a, b]) hr
    have huz : z.re ≤ 3 / 4 := hs.trans (by norm_num only [b])
    have hn : ((51 / 50 : ℂ) - z) * (51 / 50 + z) ≠ 0 := by
      intro he
      rw [he, Complex.zero_re] at hd
      nlinarith only [hd, sq_le_sq' hlz huz, sq_nonneg z.im]
    change AnalyticAt ℂ (fun u ↦ twoShiftSymmetricKernel u * (x : ℂ) ^ u) z
    unfold twoShiftSymmetricKernel
    fun_prop (disch :=
      first
      | exact pow_ne_zero _ hn
      | exact Complex.ofReal_mem_slitPlane.mpr hxp)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((a : ℂ) - T n * Complex.I)
        ((b : ℂ) + T n * Complex.I) =
      2 * Real.pi * Complex.I * H (p : ℂ) := by
    have htpos : 0 < T n := by
      dsimp only [T]; linarith only [Nat.cast_nonneg (α := ℝ) n]
    have ho :
      (p : ℂ) ∈
        AnalyticNumberTheory.RectangleGeometry.rectangleOpenBox ((a : ℂ) - T n * Complex.I)
          ((b : ℂ) + T n * Complex.I) := by
      change ((_ < _ ∧ _ < _) ∧ (_ < _ ∧ _ < _))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.sub_im,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub, min_eq_left ha,
        max_eq_right ha, min_eq_left (neg_le_self htpos.le), max_eq_right (neg_le_self htpos.le)]
      exact ⟨⟨hlP, huP⟩, neg_lt_zero.mpr htpos, htpos⟩
    apply
      AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_simple_pole
        (by
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero]
          norm_num only [a, b])
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add,
            zero_sub] using neg_lt_self htpos)
        ho
    · intro z hbox hne
      have hr := hbox.1
      change z.re ∈ Set.uIcc _ _ at hr
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Set.uIcc_of_le ha,
        Set.mem_Icc] at hr
      simp only [F, mul_assoc]
      exact
        ((differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const (p : ℂ))
              (sub_ne_zero.mpr hne)).mul
          (hH z hr.1 hr.2).differentiableAt
    · exact hH _ hlP.le huP.le
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hn : z ≠ (p : ℂ) := hz
      dsimp only [F, H]
      rw [← mul_assoc, ← mul_assoc, one_div, mul_inv_cancel₀ (sub_ne_zero.mpr hn), one_mul]
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_assoc] at h
  have he := mul_left_cancel₀ Complex.I_ne_zero h
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hi : d * (2 * (Real.pi : ℂ)) = 1 := by
    dsimp only [d]
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat, one_div,
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
  have hh := congrArg (fun u ↦ d * u) he
  rw [mul_sub, ← mul_assoc, hi, one_mul] at hh
  simpa only [twoShiftSymmetricPole, F, K, H, a, b, d, twoShiftSymmetricMellin, mul_comm Complex.I,
    mul_assoc] using hh

/-- For a nonnegative frequency the two right-line pole terms in the even
comparison move to the left line, each subtracting its weighted residue. -/
theorem twoShift_even_difference_left {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let H := fun s : ℂ ↦ twoShiftSymmetricKernel s * (x : ℂ) ^ s
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      (∑' n, twoShiftSymmetricMellin.summand ψ x n).re
    twoShiftEvenDifference χ b =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ∫ t : ℝ,
                  (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) -
                      1 / w t -
                      1 / (w t - 1)) *
                    H (l t)).re -
            (twoShiftSymmetricPole (-9 / 16) (-1 / 2) x).re -
            (twoShiftSymmetricPole (-9 / 16) (1 / 2) x).re -
            (H ((-1 / 2 : ℝ) : ℂ)).re -
            (H ((1 / 2 : ℝ) : ℂ)).re +
          S (1 : DirichletCharacter ℂ 1) -
        S χ := by
  intro x l w H S
  have hx : 1 ≤ x := Real.one_le_exp hb
  have hp (p : ℝ) (hl : -9 / 16 < p) (hu : p < 9 / 16) :=
    congrArg Complex.re (twoShift_symmetric_pole_difference hx hl hu)
  have hm := hp (-1 / 2) (by norm_num only) (by norm_num only)
  have hpos := hp (1 / 2) (by norm_num only) (by norm_num only)
  simp only [Complex.sub_re] at hm hpos
  unfold twoShiftEvenDifference
  dsimp only
  unfold twoShiftSymmetricPole at hm hpos ⊢
  dsimp only at hm hpos ⊢
  dsimp only [H, S, w, l, x] at *
  linarith only [hm, hpos]

/-- At each point of the left line the reflected rational terms have positive
coefficients at both half-unit poles. -/
theorem twoShift_left_pole_split (s W C L Z : ℂ) :
    let w := -s + 1 / 2
    (C + L - Z - 1 / w - 1 / (w - 1)) * W =
      C * W + (-Z * W - -L * W) + (1 / (s - ((1 / 2 : ℝ) : ℂ))) * W +
        (1 / (s - ((-1 / 2 : ℝ) : ℂ))) * W := by
  intro w
  have hp : w = -(s - ((1 / 2 : ℝ) : ℂ)) := by
    dsimp only [w]; push_cast; ring
  have hm : w - 1 = -(s - ((-1 / 2 : ℝ) : ℂ)) := by
    dsimp only [w]; push_cast; ring
  rw [hm, hp, div_neg, div_neg]
  ring

/-- The left comparison integral splits into the conductor, the reflected
Euler difference, and the two simple-pole integrals at positive scale. -/
theorem twoShift_left_integral_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ -(s t) + 1 / 2
    let W := fun t : ℝ ↦ twoShiftSymmetricKernel (s t) * (x : ℂ) ^ s t
    let C := fun t : ℝ ↦ Complex.log q * W t
    let A := fun {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) (t : ℝ) ↦
      -logDeriv ψ.LFunction (w t) * W t
    let P := fun (p t : ℝ) ↦ (1 / (s t - (p : ℂ))) * W t
    (∫ t : ℝ,
        (Complex.log q + logDeriv χ.LFunction (w t) - logDeriv riemannZeta (w t) - 1 / w t -
            1 / (w t - 1)) *
          W t) =
      (∫ t : ℝ, C t) + (∫ t : ℝ, A (1 : DirichletCharacter ℂ 1) t - A χ t) +
        (∫ t : ℝ, P (1 / 2) t) +
        ∫ t : ℝ, P (-1 / 2) t := by
  intro s w W C A P
  have hW := twoShift_symmetric_line (c := -9 / 16) (by norm_num only) (by norm_num only)
  have hc : Continuous (fun t : ℝ ↦ (x : ℂ) ^ s t) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hi : MeasureTheory.Integrable W := by
    apply hW.mul_bdd (c := x ^ (-9 / 16 : ℝ)) hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, twoShift_line_re]
  have hC : MeasureTheory.Integrable C := hi.const_mul _
  have hA :=
    (twoShift_reflected_integrable (1 : DirichletCharacter ℂ 1) hx).sub
      (twoShift_reflected_integrable χ hx)
  have hP (p : ℝ) (hne : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    simpa only [P, W, s, mul_assoc, twoShiftSymmetricMellin] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line twoShiftSymmetricMellin
        (by
          change -1 / 2 - (1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (-9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hne hx
  have hp := hP (1 / 2) (by norm_num only)
  have hm := hP (-1 / 2) (by norm_num only)
  let B := fun t : ℝ ↦ A (1 : DirichletCharacter ℂ 1) t - A χ t
  change MeasureTheory.Integrable B at hA
  have he (t : ℝ) :=
    twoShift_left_pole_split (s t) (W t) (Complex.log q) (logDeriv χ.LFunction (w t))
      (logDeriv riemannZeta (w t))
  calc
    _ = ∫ t : ℝ, ((C + B) + P (1 / 2) + P (-1 / 2)) t := by
      apply MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
      simpa only [C, B, A, P, Pi.add_apply, DirichletCharacter.LFunction_modOne_eq] using he t
    _ = _ := by
      calc
        _ = _ := MeasureTheory.integral_add ((hC.add hA).add hp) hm
        _ = _ := congrArg (· + _) (MeasureTheory.integral_add (hC.add hA) hp)
        _ = _ := congrArg (fun z ↦ z + _ + _) (MeasureTheory.integral_add hC hA)

/-- For a nonnegative frequency the contour comparison consists of the conductor,
the reflected and forward Euler differences, and the two weighted residues. -/
theorem twoShift_even_difference_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) :
    let x := Real.exp b
    let H := fun p : ℝ ↦ (twoShiftSymmetricKernel (p : ℂ) * (x : ℂ) ^ (p : ℂ)).re
    let R := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      ∑' n : ℕ,
        (ψ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n * x))
    let S := fun {m : ℕ} (ψ : DirichletCharacter ℂ m) ↦
      (∑' n, twoShiftSymmetricMellin.summand ψ x n).re
    let ψ := (1 : DirichletCharacter ℂ 1)
    twoShiftEvenDifference χ b =
      (Complex.log q * (twoShiftSymmetricProfile x⁻¹ : ℂ)).re + (R ψ - R χ) - H (-1 / 2) -
            H (1 / 2) +
          S ψ -
        S χ := by
  intro x H R S ψ
  have hx : 0 < x := Real.exp_pos b
  have hw (t : ℝ) :
    ((17 / 16 : ℝ) : ℂ) - Complex.I * t = -(((-9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2 := by
    push_cast
    ring
  have h := twoShift_even_difference_left χ hb
  dsimp only at h
  simp_rw [hw] at h
  have hs := twoShift_left_integral_split χ hx
  dsimp only at hs
  rw [hs] at h
  simp only [mul_add, Complex.add_re] at h
  have hc := twoShift_left_conductor q hx
  have ha := twoShift_reflected_euler_difference χ hx
  dsimp only at hc ha
  rw [hc, ha] at h
  unfold twoShiftSymmetricPole at h
  dsimp only at h
  dsimp only [x, H, R, S, ψ] at *
  linarith only [h]

/-- The ordinary Euler sum for the symmetric profile at positive scale y. -/
noncomputable def twoShiftProfileSum {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) : ℝ :=
  ∑' n : ℕ,
    (χ n).re * (ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n / y))

/-- The integral-free character comparison at frequency b uses the same
profile sum at reciprocal scales, together with the conductor and residues. -/
noncomputable def twoShiftProfileDifference {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) : ℝ :=
  let x := Real.exp b
  let H := fun p : ℝ ↦ (twoShiftSymmetricKernel (p : ℂ) * (x : ℂ) ^ (p : ℂ)).re
  let E := fun y ↦ twoShiftProfileSum (1 : DirichletCharacter ℂ 1) y - twoShiftProfileSum χ y
  (Complex.log q * (twoShiftSymmetricProfile x⁻¹ : ℂ)).re + E x⁻¹ - H (-1 / 2) - H (1 / 2) + E x

/-- At every nonnegative frequency both ordinary Euler differences are
weighted by the explicit real profile. -/
theorem twoShift_even_difference_profile {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hb : 0 ≤ b) : twoShiftEvenDifference χ b = twoShiftProfileDifference χ b := by
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    (∑' n, twoShiftSymmetricMellin.summand ψ (Real.exp b) n).re =
      twoShiftProfileSum ψ (Real.exp b) := by
    rw [Complex.re_tsum
        (LLS.PaperStatements.MellinKernel.summable_summand twoShiftSymmetricMellin ψ
          (Real.exp_pos b))]
    exact tsum_congr (twoShift_symmetric_summand ψ (Real.exp_pos b))
  have h := twoShift_even_difference_euler χ hb
  dsimp only at h
  rw [hs, hs] at h
  simp only [twoShiftProfileDifference, twoShiftProfileSum, div_inv_eq_mul] at h ⊢
  linarith only [h]

/-- The four-frequency mass comparison retains only the common xi term at
zero frequency and the four explicit real profile differences. -/
theorem twoShift_compared_mass_profile {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    twoShiftComparedMass χ =
      twoShiftXiContourValue 0 + 5 / 4 * twoShiftProfileDifference χ 0 -
            1 / 2 * twoShiftProfileDifference χ (14 / 5) +
          1 / 2 * twoShiftProfileDifference χ 3 -
        1 / 4 * twoShiftProfileDifference χ (1 / 5) := by
  unfold twoShiftComparedMass
  rw [twoShift_even_difference_profile χ (le_refl 0),
    twoShift_even_difference_profile χ (b := 14 / 5) (by norm_num only),
    twoShift_even_difference_profile χ (b := 3) (by norm_num only),
    twoShift_even_difference_profile χ (b := 1 / 5) (by norm_num only)]

/-- When the character is one on primes through X, its symmetric Euler deficit
is supported above floor X at every positive scale. -/
theorem twoShift_profile_tail_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X y : ℝ}
    (hX : 0 ≤ X) (hy : 0 < y) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    twoShiftProfileSum (1 : DirichletCharacter ℂ 1) y - twoShiftProfileSum χ y =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n },
        (1 - (χ n.val).re) *
          (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
            twoShiftSymmetricProfile (n.val / y)) := by
  let W := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n / y)
  have hs {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (ψ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand twoShiftSymmetricMellin ψ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun
          (fun n ↦ (twoShift_symmetric_summand ψ hy n).symm)).summable
  unfold twoShiftProfileSum
  rw [← (hs (1 : DirichletCharacter ℂ 1)).tsum_sub (hs χ)]
  let F := fun n : ℕ ↦ (1 - (χ n).re) * W n
  have he (n : ℕ) : ((1 : DirichletCharacter ℂ 1) n).re * W n - (χ n).re * W n = F n := by
    simp only [F, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, sub_mul]
  rw [tsum_congr he]
  symm
  apply tsum_subtype_eq_of_support_subset (f := F) (s := {n : ℕ | ⌊X⌋₊ < n})
  intro n hn
  by_contra hno
  have hcut := (Nat.le_floor_iff hX).mp (le_of_not_gt hno)
  apply hn
  by_cases hm : ArithmeticFunction.vonMangoldt n = 0
  · simp only [F, W, hm, zero_div, zero_mul, mul_zero]
  simp only [F,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ hp hcut hm,
    Complex.one_re, sub_self, zero_mul]

/-- The two Euler tails beyond X and the explicit conductor and residues
at frequency b, after all passing prime bases have been removed. -/
noncomputable def twoShiftTailDifference {q : ℕ} (χ : DirichletCharacter ℂ q) (X b : ℝ) : ℝ :=
  let x := Real.exp b
  let E := fun y : ℝ ↦
    ∑' n : { n : ℕ // ⌊X⌋₊ < n },
      (1 - (χ n.val).re) *
        (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
          twoShiftSymmetricProfile (n.val / y))
  let H := fun p : ℝ ↦ (twoShiftSymmetricKernel (p : ℂ) * (x : ℂ) ^ (p : ℂ)).re
  (Complex.log q * (twoShiftSymmetricProfile x⁻¹ : ℂ)).re + E x⁻¹ - H (-1 / 2) - H (1 / 2) + E x

/-- Passage through X removes the entire prefix at both reciprocal scales. -/
theorem twoShift_difference_eq_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X : ℝ}
    (hX : 0 ≤ X) (hp : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) (b : ℝ) :
    twoShiftProfileDifference χ b = twoShiftTailDifference χ X b := by
  unfold twoShiftProfileDifference twoShiftTailDifference
  dsimp only
  rw [twoShift_profile_tail_eq χ hX (inv_pos.mpr (Real.exp_pos b)) hp,
    twoShift_profile_tail_eq χ hX (Real.exp_pos b) hp]

/-- At a fixed frequency the three pair conductors contribute twice log n
times the profile. Each residue occurs three times, at the same scale. -/
theorem twoShift_three_tail_sum {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hn : n = p * q * r)
    (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) (X t : ℝ) :
    let x := Real.exp t
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) (y : ℝ) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k },
        (1 - (χ k.val).re) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
            twoShiftSymmetricProfile (k.val / y))
    let T := fun y ↦ E a y + E b y + E c y
    let H := fun s : ℝ ↦ (twoShiftSymmetricKernel (s : ℂ) * (x : ℂ) ^ (s : ℂ)).re
    twoShiftTailDifference a X t + twoShiftTailDifference b X t + twoShiftTailDifference c X t =
      2 * Real.log n * twoShiftSymmetricProfile x⁻¹ + T x⁻¹ + T x -
        3 * (H (-1 / 2) + H (1 / 2)) := by
  intro x E T H
  unfold twoShiftTailDifference
  dsimp only [T, E, H, x]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.log_re, Complex.norm_natCast]
  linear_combination (twoShiftSymmetricProfile (Real.exp t)⁻¹) * pair_level_log_sum hn

/-- At a positive integer argument the two reciprocal scales in the Euler tail
give the forward and reflected profiles of the cosine inversion formula. -/
theorem twoShift_tail_profile_pair (u s : ℝ) :
    twoShiftSymmetricProfile (u / (Real.exp s)⁻¹) + twoShiftSymmetricProfile (u / Real.exp s) =
      twoShiftSymmetricProfile (u * Real.exp (-s)) +
        twoShiftSymmetricProfile (u⁻¹ * Real.exp (-s)) := by
  have hinv (v : ℝ) : twoShiftSymmetricProfile v⁻¹ = twoShiftSymmetricProfile v := by
    simp only [twoShiftSymmetricProfile, Real.log_inv, abs_neg]
  rw [Real.exp_neg, div_inv_eq_mul, div_eq_mul_inv, ← mul_inv, hinv, add_comm]

/-- After subtracting the zero-frequency weight, the signed four-frequency
tail at both scales is precisely the cosine inverse correction. -/
theorem twoShift_tail_cosine_eq {u : ℝ} (hu : 0 < u) :
    let P := fun s : ℝ ↦
      twoShiftSymmetricProfile (u / (Real.exp s)⁻¹) + twoShiftSymmetricProfile (u / Real.exp s)
    let D := fun v : ℝ ↦
      (Analysis.inverseMellin twoShiftCosineKernel 0 v).re - twoShiftSymmetricProfile v
    5 / 4 * P 0 - 1 / 2 * P (14 / 5) + 1 / 2 * P 3 - 1 / 4 * P (1 / 5) = P 0 + (D u + D u⁻¹) := by
  intro P D
  simp only [P, twoShift_tail_profile_pair, D, twoShift_cosine_inversion hu,
    twoShift_cosine_inversion (inv_pos.mpr hu), Complex.ofReal_re, neg_zero, Real.exp_zero, mul_one]
  ring

/-- For the actual pair of reciprocal scales, the four-frequency Euler tail
in excess of the unshifted tail costs less than 0.327988 under RH. -/
theorem twoShift_tail_cosine_bound {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ} (hX : 85264 ≤ X)
    (hRH : RiemannHypothesis) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let P := fun (u s : ℝ) ↦
      twoShiftSymmetricProfile (u / (Real.exp s)⁻¹) + twoShiftSymmetricProfile (u / Real.exp s)
    (∑' k : { n : ℕ // ⌊X⌋₊ < n },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
          (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
            (5 / 4 * P k.val 0 - 1 / 2 * P k.val (14 / 5) + 1 / 2 * P k.val 3 -
              1 / 4 * P k.val (1 / 5) -
              P k.val 0))) <
      327988 / 1000000 := by
  intro P
  apply lt_of_eq_of_lt _ (twoShift_inverse_tail_bound a b c hX hRH ht)
  apply tsum_congr
  intro k
  have hk : 0 < (k.val : ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt k.property)
  have h := twoShift_tail_cosine_eq hk
  dsimp only at h
  dsimp only [P]
  rw [h, add_sub_cancel_left]

/-- At one positive scale the three absolutely convergent character tails
combine into one series weighted by three minus the trace. -/
theorem twoShift_trace_tail_hasSum {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    HasSum
      (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val)
      (E a + E b + E c) := by
  intro W E
  have hs {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun n : ℕ ↦ (χ n).re * W n) := by
    have h := LLS.PaperStatements.MellinKernel.summable_summand twoShiftSymmetricMellin χ hy
    exact
      ((Complex.hasSum_re h.hasSum).congr_fun
          (fun n ↦ (twoShift_symmetric_summand χ hy n).symm)).summable
  have hW : Summable W := by
    apply (hs (1 : DirichletCharacter ℂ 1)).congr
    intro n
    simp only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  have hE {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) :
    Summable (fun k : { k : ℕ // ⌊X⌋₊ < k } ↦ (1 - (χ k.val).re) * W k.val) := by
    apply ((hW.sub (hs χ)).subtype _).congr
    intro k
    change W k.val - (χ k.val).re * W k.val = _
    rw [sub_mul, one_mul]
  dsimp only [E]
  apply (((hE a).hasSum.add (hE b).hasSum).add (hE c).hasSum).congr_fun
  intro k
  ring

/-- Summing the trace-weighted series recovers the three individual tails. -/
theorem twoShift_trace_tail_eq {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    {y : ℝ} (hy : 0 < y) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile (n / y)
    let E := fun {m : ℕ} (χ : DirichletCharacter ℂ m) ↦
      ∑' k : { k : ℕ // ⌊X⌋₊ < k }, (1 - (χ k.val).re) * W k.val
    E a + E b + E c =
      ∑' k : { k : ℕ // ⌊X⌋₊ < k },
        (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val := by
  exact (twoShift_trace_tail_hasSum a b c X hy).tsum_eq.symm

/-- For cutoffs at least 85264 the four-frequency sum equals its zero-frequency term
plus the common Euler correction, preserving the signed tail for the phase estimate. -/
theorem twoShift_paired_tail_eq {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) :
    let F := fun (y : ℝ) (k : { k : ℕ // ⌊X⌋₊ < k }) ↦
      (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
        (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
          twoShiftSymmetricProfile (k.val / y))
    let S := fun s : ℝ ↦ (∑' k, F (Real.exp s)⁻¹ k) + ∑' k, F (Real.exp s) k
    5 / 4 * S 0 - 1 / 2 * S (14 / 5) + 1 / 2 * S 3 - 1 / 4 * S (1 / 5) =
      S 0 +
        ∑' k : { n : ℕ // ⌊X⌋₊ < n },
          (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
            (ArithmeticFunction.vonMangoldt k.val / (k.val : ℝ) ^ (38 / 25 : ℝ) *
              twoShiftEulerPoly (Real.log k.val)) := by
  intro F S
  have hs (s : ℝ) : HasSum (fun k ↦ F (Real.exp s)⁻¹ k + F (Real.exp s) k) (S s) :=
    (twoShift_trace_tail_hasSum a b c X (inv_pos.mpr (Real.exp_pos s))).summable.hasSum.add
      (twoShift_trace_tail_hasSum a b c X (Real.exp_pos s)).summable.hasSum
  have h :=
    (((((hs 0).mul_left (5 / 4)).sub ((hs (14 / 5)).mul_left (1 / 2))).add
              ((hs 3).mul_left (1 / 2))).sub
          ((hs (1 / 5)).mul_left (1 / 4))).sub
      (hs 0)
  have he := twoShift_inverse_tail_eq a b c hX
  dsimp only at he
  apply sub_eq_iff_eq_add'.mp
  rw [← h.tsum_eq, ← he]
  apply tsum_congr
  intro k
  have hk := twoShift_tail_cosine_eq (Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt k.property))
  dsimp only at hk
  dsimp only [F]
  linear_combination
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val) *
      hk

/-- At four frequencies the signed sum of the paired Euler series exceeds
its zero-frequency value by less than the certified cosine correction. -/
theorem twoShift_paired_tail_bound {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) (hRH : RiemannHypothesis) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let F := fun (y : ℝ) (k : { k : ℕ // ⌊X⌋₊ < k }) ↦
      (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
        (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
          twoShiftSymmetricProfile (k.val / y))
    let S := fun s : ℝ ↦ (∑' k, F (Real.exp s)⁻¹ k) + ∑' k, F (Real.exp s) k
    5 / 4 * S 0 - 1 / 2 * S (14 / 5) + 1 / 2 * S 3 - 1 / 4 * S (1 / 5) <
      S 0 + 327988 / 1000000 := by
  intro F S
  rw [twoShift_paired_tail_eq a b c hX]
  have h := three_trace_tail_large a b c hX hRH ht
  dsimp only at h
  linarith only [h]

/-- At scale one the three-character deficit is at most four times the
unsigned tail. Nonnegativity of the symmetric profile preserves the trace bound. -/
theorem twoShift_unshifted_tail_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X : ℝ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile n
    (∑' k : { n : ℕ // ⌊X⌋₊ < n }, (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) * W k.val) ≤
      4 * ∑' k : { n : ℕ // ⌊X⌋₊ < n }, W k.val := by
  intro W
  have h := (twoShift_trace_tail_hasSum a b c X (y := 1) zero_lt_one).summable
  simp only [div_one] at h
  have hW : Summable W := by
    have h1 :=
      LLS.PaperStatements.MellinKernel.summable_summand twoShiftSymmetricMellin
        (1 : DirichletCharacter ℂ 1) (x := 1) zero_lt_one
    apply (Complex.hasSum_re h1.hasSum).summable.congr
    intro n
    simpa only [MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul,
      div_one] using twoShift_symmetric_summand (1 : DirichletCharacter ℂ 1) zero_lt_one n
  rw [← tsum_mul_left]
  apply h.tsum_le_tsum _ ((hW.subtype _).mul_left 4)
  intro k
  apply mul_le_mul_of_nonneg_right (by linarith only [ht k.val])
  dsimp only [W, twoShiftSymmetricProfile]
  positivity

/-- At scale one, the two equal symmetric weights reproduce the section 31
Euler weight, including the vanishing von Mangoldt term at zero. -/
theorem twoShift_unshifted_euler_weight (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * twoShiftSymmetricProfile n =
      (1 / 2 : ℝ) * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, zero_div, zero_mul, mul_zero]
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hd : (n : ℝ) ^ (38 / 25 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (51 / 50 : ℝ) := by
    rw [← Real.rpow_add hp]
    norm_num only
  unfold twoShiftSymmetricProfile quarterEulerWeight570
  dsimp only
  rw [abs_of_nonneg (Real.log_natCast_nonneg n), mul_comm (-(51 / 50)) (Real.log n), ←
    Real.rpow_def_of_pos hp, Real.rpow_neg hp.le, Real.sqrt_eq_rpow, hd]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The unsigned budget at frequency zero is four times the section 31 Euler
tail, with the same strict integer cutoff. -/
theorem twoShift_unshifted_euler_tail (X : ℝ) :
    8 *
        (∑' k : { n : ℕ // ⌊X⌋₊ < n },
          ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val * twoShiftSymmetricProfile k.val) =
      4 *
        (∑' k : { n : ℕ // ⌊X⌋₊ < n },
          ArithmeticFunction.vonMangoldt k.val * quarterEulerWeight570 k.val) := by
  simp_rw [twoShift_unshifted_euler_weight]
  rw [tsum_mul_left]
  ring

/-- At both half-unit poles the symmetric kernel has the same rational
value. The two real residues depend on the scale only through its powers. -/
theorem twoShift_real_residue_pair {x : ℝ} (hx : 0 ≤ x) :
    (twoShiftSymmetricKernel ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re +
        (twoShiftSymmetricKernel ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re =
      ((51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3) * (x ^ (-1 / 2 : ℝ) + x ^ (1 / 2 : ℝ)) := by
  let K := (51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3
  have hp : twoShiftSymmetricKernel ((1 / 2 : ℝ) : ℂ) = (K : ℂ) := by
    unfold twoShiftSymmetricKernel K
    push_cast
    norm_num only
  have hm : twoShiftSymmetricKernel ((-1 / 2 : ℝ) : ℂ) = (K : ℂ) := by
    rw [show ((-1 / 2 : ℝ) : ℂ) = -((1 / 2 : ℝ) : ℂ) by
        push_cast; ring,
      twoShift_symmetric_neg, hp]
  rw [hp, hm, ← Complex.ofReal_cpow hx, ← Complex.ofReal_cpow hx]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re, mul_add, K]

/-- At nonnegative frequency the reciprocal-scale conductor profile has
an explicit exponential factor and a quadratic polynomial in the frequency. -/
theorem twoShift_conductor_profile {b : ℝ} (hb : 0 ≤ b) :
    twoShiftSymmetricProfile (Real.exp b)⁻¹ =
      Real.exp (-(51 / 50) * b) *
        (3 / 16 + (3 * (51 / 50) / 16) * b + ((51 / 50) ^ 2 / 16) * b ^ 2) := by
  simp only [twoShiftSymmetricProfile, Real.log_inv, Real.log_exp, abs_neg, abs_of_nonneg hb]

/-- Under RH the zero-frequency xi contour is the absolute sixth-pole zeta
mass, so the section 96 allowance also bounds this contour. -/
theorem twoShift_xi_zero_small (hRH : RiemannHypothesis) :
    twoShiftXiContourValue 0 < 1 / 12500 := by
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm twoShiftSymmetricMellin hRH
      (Real.exp_pos 0)
  have h :=
    (congrArg Complex.re (twoShift_symmetric_xi_contour hRH (le_refl 0))).symm.trans
      (Complex.re_tsum hs)
  apply lt_of_eq_of_lt (h.trans (tsum_congr fun ρ ↦ ?_)) (twoShift_zeta_mass_small hRH)
  simp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm, Real.exp_zero,
    Complex.ofReal_one, Complex.one_cpow, mul_one,
    LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, norm_mul, Complex.norm_natCast]
  change ((_ : ℂ) * twoShiftSymmetricKernel (Complex.I * (ρ : ℂ).im)).re = _
  rw [twoShift_symmetric_axis, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re,
    quarter_zero_norm_570]

/-- At unshifted scale at least one, the contour contribution of an even,
self-inverse nonprincipal character equals the principal prime sum plus
the two-pole residue expression under RH. -/
theorem twoShift_unshifted_contour_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    contourNonEuler570 χ x - reflectedIntegral570 χ x =
      (∑' n : ℕ, quarterKernel570.summand (1 : DirichletCharacter ℂ 1) x n).re +
        twoShiftResidueValue χ x := by
  have h := twoShift_even_zeta_cancel χ he (zero_lt_one.trans_le hx)
  rw [hi] at h
  unfold twoShiftResidueValue
  linarith only [h, twoShift_reflected_residues χ hn he hRH hx]

/-- At the same cutoff X, the unshifted reflected tail costs at most the
tail at scale X exp(-3), by monotonicity of the scaled fifth power. -/
theorem twoShift_dual_unshifted_numeric (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X) :
    (∑' n : { n : ℕ // ⌊X⌋₊ < n }, twoShiftDualWeight X n.val) < 5262 / 1000000 := by
  have hx : 1 ≤ X := by linarith only [hX]
  have hx0 := zero_lt_one.trans_le hx
  have he (k : ℕ) : Real.exp (k * (1 : ℝ)) ≤ (3 : ℝ) ^ k := by
    rw [Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le k
  have h6 : 6 ≤ Real.log X := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    have h := he 6
    norm_num only at h
    linarith only [h, hX]
  have hy : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have h := he 3
    norm_num only at h
    linarith only [h, hX]
  let Y := X * Real.exp 3
  have hY : 0 < Y := mul_pos hx0 (Real.exp_pos _)
  have hYX : Y * Real.exp (-3) = X := by
    rw [show Y = X * Real.exp 3 from rfl, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      mul_one]
  have hlog : Real.log X ≤ Real.log Y := by
    rw [show Y = X * Real.exp 3 from rfl, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
    linarith only
  apply lt_of_le_of_lt _ (twoShift_dual_tail_numeric hRH hX)
  apply
    ((dual_weight_hasSum hx0).summable.subtype _).tsum_le_tsum _
      ((dual_weight_hasSum (zero_lt_one.trans_le hy)).summable.subtype _)
  intro k
  have hd := twoShift_dual_density hY (hYX.symm ▸ hx) k.val
  rw [hYX] at hd
  simp only [Function.comp_apply, hd, twoShift_dual_density hx0 hy]
  unfold twoShiftReflectedDensity
  have hmono := reflected_shift_antitone (Real.log_natCast_nonneg k.val) h6 (h6.trans hlog) hlog
  dsimp only at hmono
  have hc :
    0 ≤
      (51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) *
        ArithmeticFunction.vonMangoldt k.val *
        (k.val : ℝ) ^ (-(38 / 25 : ℝ)) := by
    positivity
  convert mul_le_mul_of_nonneg_left hmono hc using 1 <;> ring

/-- The positive half-pole cancels the full-kernel part of the outer mass
bound at X, leaving the conductor and the negative half-pole. -/
theorem twoShift_principal_mass_cancel (n : ℕ) (X : ℝ) :
    4 * (Real.sqrt X * ((3 * (quarterKernel570.function (1 / 2)).re - 717289 / 1000000) / 4)) +
        twoShiftRealMain n X =
      2 * Real.log n * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) X⁻¹ -
        3 * ((50 / 51) * Real.exp (-(7 / 5)) / (1 - 25 / 51) ^ 6 * X ^ (-1 / 2 : ℝ)) -
        717289 / 1000000 * Real.sqrt X := by
  rw [quarterKernel570, LLS.PaperStatements.rationalPole_half_value, twoShiftRealMain,
    Real.sqrt_eq_rpow]
  norm_num only [Nat.reduceMul]
  ring

/-- At a nonnegative fixed frequency the absolute sixth-pole zero mass
weighted by the cosine equals the corresponding real symmetric contour. -/
theorem twoShift_cosine_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    {X b : ℝ} (hx : 0 < X) (hb : 0 ≤ b) :
    (∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (b * ρ.im)) =
      twoShiftContourValue χ b := by
  unfold twoShiftContourValue
  rw [← twoShift_symmetric_contour hq hG hp hn hb,
    Complex.re_tsum
      (LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm twoShiftSymmetricMellin hq hG
        hp hn (inv_ne_one.mpr hn) (Real.exp_pos b))]
  apply tsum_congr
  intro ρ
  rw [LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ hx ρ,
    kernel_zero_norm_570 hn, twoShift_symmetric_zero_re, quarter_zero_norm_570]

/-- Under GRH the zero-frequency symmetric contour is the unweighted
absolute zero mass. This removes the common unshifted term from the phase gain. -/
theorem twoShift_mass_eq_zero_contour {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1) :
    quarterMass570 χ = twoShiftContourValue χ 0 := by
  rw [← twoShift_cosine_contour hq hG hp hn zero_lt_one (le_refl (0 : ℝ))]
  simp only [zero_mul, Real.cos_zero, mul_one,
    LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ zero_lt_one]
  exact tsum_congr (fun ρ ↦ (kernel_zero_norm_570 hn ρ).symm)

/-- For an even self-inverse primitive character which is one on primes
through X, a fixed-frequency cosine sum equals the common xi contour,
its conductor and poles, and the two Euler tails above X. -/
theorem twoShift_cosine_eq_tail {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {X b : ℝ} (hx : 0 < X) (hb : 0 ≤ b)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1) :
    (∑' ρ : ℂ, ‖quarterKernel570.oscillatingZeroTerm χ X ρ‖ * Real.cos (b * ρ.im)) =
      twoShiftXiContourValue b + twoShiftTailDifference χ X b := by
  rw [twoShift_cosine_contour hq hG hp hn hx hb]
  have hc := twoShift_even_difference_eq hp hn hi he b
  rw [twoShift_even_difference_profile χ hb, twoShift_difference_eq_tail χ hx.le hpass] at hc
  linarith only [hc]

/-- The two reciprocal Euler tails at a fixed frequency, combined before
applying the common three-character trace. -/
@[expose]
noncomputable def twoShiftCosineTail {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (X s : ℝ) : ℝ :=
  let F := fun (y : ℝ) (k : { k : ℕ // ⌊X⌋₊ < k }) ↦
    (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
      (ArithmeticFunction.vonMangoldt k.val / Real.sqrt k.val *
        twoShiftSymmetricProfile (k.val / y))
  (∑' k, F (Real.exp s)⁻¹ k) + ∑' k, F (Real.exp s) k

/-- The three symmetric contour differences share the same two real residues.
Their arithmetic terms form the signed common trace tail. -/
theorem twoShift_three_cosine_tail {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) (X s : ℝ) :
    twoShiftTailDifference a X s + twoShiftTailDifference b X s + twoShiftTailDifference c X s =
      2 * Real.log n * twoShiftSymmetricProfile (Real.exp s)⁻¹ -
          6 * ((51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3) * Real.cosh (s / 2) +
        twoShiftCosineTail a b c X s := by
  have h := twoShift_three_tail_sum hn a b c X s
  dsimp only at h
  rw [twoShift_real_residue_pair (Real.exp_pos s).le] at h
  simp only [Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp] at h
  dsimp only [twoShiftCosineTail]
  rw [Real.cosh_eq]
  have ha := twoShift_trace_tail_eq a b c X (inv_pos.mpr (Real.exp_pos s))
  have hb := twoShift_trace_tail_eq a b c X (Real.exp_pos s)
  dsimp only at ha hb
  rw [show s * (-1 / 2 : ℝ) = -(s / 2) by ring, show s * (1 / 2 : ℝ) = s / 2 by ring] at h
  linear_combination h + ha + hb

/-- The two-frequency contour part separates into the fixed cosine
combination and the shifted residues after the principal prime sums cancel. -/
theorem twoShift_part_eq_residues {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {X : ℝ} (hx : 0 < X) (ht : 1 ≤ X * Real.exp (-3)) :
    twoShiftContourPart χ X - twoShiftPrincipalDiff X =
      (twoShiftContourValue χ (14 / 5) - twoShiftContourValue χ 3) / 2 -
          (twoShiftContourValue χ 0 - twoShiftContourValue χ (1 / 5)) / 4 +
        (twoShiftResidueValue χ (X * Real.exp (-(14 / 5))) -
            twoShiftResidueValue χ (X * Real.exp (-3))) /
          2 := by
  have hb :=
    ht.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num only : (-3 : ℝ) ≤ -(14 / 5)))
        hx.le)
  unfold twoShiftContourPart twoShiftPrincipalDiff
  dsimp only
  rw [twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 14 / 5),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 3),
    twoShift_cosine_contour hq hG hp hn hx (by norm_num only : (0 : ℝ) ≤ 1 / 5),
    twoShift_mass_eq_zero_contour hq hG hp hn,
    twoShift_unshifted_contour_eq χ hn hi he hG.riemann hb,
    twoShift_unshifted_contour_eq χ hn hi he hG.riemann ht]
  ring

/-- Under prime-prefix passage, the three pair phases dominate the fixed
cosine combination and the difference of the three shifted residue values. -/
theorem twoShift_triple_phase_components {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hn : 1 < n) (ho : Odd n) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hpq : p * q ∣ n) (hpr : p * r ∣ n) (hqr : q * r ∣ n) (hpk : p - 1 ∣ n - 1)
    (hqk : q - 1 ∣ n - 1) (hrk : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let W := fun s ↦ twoShiftContourValue a s + twoShiftContourValue b s + twoShiftContourValue c s
    let R := fun x ↦ twoShiftResidueValue a x + twoShiftResidueValue b x + twoShiftResidueValue c x
    (W (14 / 5) - W 3) / 2 - (W 0 - W (1 / 5)) / 4 +
        (R (X * Real.exp (-(14 / 5))) - R (X * Real.exp (-3))) / 2 ≤
      twoShiftZeroPhase a X + twoShiftZeroPhase b X + twoShiftZeroPhase c X := by
  intro a b c W R
  have hx : 0 < X := by linarith only [hX]
  have ht : 1 ≤ X * Real.exp (-3) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    rw [← Real.exp_natCast_mul] at he
    norm_num only [Nat.cast_ofNat, mul_one] at he
    linarith only [he, hX]
  have H {i j : ℕ} [NeZero i] [NeZero j] [Fact i.Prime] [Fact j.Prime] [Fact (2 < i)] [Fact (2 < j)]
    (hi : Odd i) (hj : Odd j) (hd : i * j ∣ n) (hik : i - 1 ∣ n - 1) (hjk : j - 1 ∣ n - 1)
    (hv : padicValNat 2 (j - 1) = padicValNat 2 (i - 1)) :=
    twoShift_part_eq_residues
      ((Fact.out : i.Prime).two_le.trans (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)) hG
      (pair_character_primitive hsq hd (hi.mul hj))
      (pair_character_ne_one hsq hd (hi.mul hj)
        ((Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)))
      (NumberTheory.complexJacobiNumeratorCharacter_isQuadratic _ _).inv
      (pair_character_even_of_korselt hn ho hi hj hik hjk hv) hx ht
  have h := twoShift_pair_zero_lower hsq hn ho hp hq hr hpq hpr hqr hpk hqk hrk hvq hvr hG hX hpass
  dsimp only [W, R, a, b, c] at h ⊢
  linarith only [h, H hp hq hpq hpk hqk hvq, H hp hr hpr hpk hrk hvr,
    H hq hr hqr hqk hrk (hvr.trans hvq.symm)]

/-- The four-frequency Euler contribution is the negative signed trace
tail. Its zero-frequency term cancels before any bound is applied. -/
theorem twoShift_cosine_tail_combination {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) :
    let S := twoShiftCosineTail a b c X
    (S (14 / 5) - S 3) / 2 - (S 0 - S (1 / 5)) / 4 =
      -(∑' k : { n : ℕ // ⌊X⌋₊ < n },
          (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
            (ArithmeticFunction.vonMangoldt k.val / (k.val : ℝ) ^ (38 / 25 : ℝ) *
              twoShiftEulerPoly (Real.log k.val))) := by
  intro S
  have h := twoShift_paired_tail_eq a b c hX
  dsimp only [S, twoShiftCosineTail] at h ⊢
  linarith only [h]

/-- Under prime-prefix passage, the symmetric contour equals the common xi
contour plus the conductor, pole and Euler expression at that frequency. -/
theorem twoShift_contour_eq_tail {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {X s : ℝ} (hx : 0 ≤ X)
    (hs : 0 ≤ s) (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1) :
    twoShiftContourValue χ s = twoShiftXiContourValue s + twoShiftTailDifference χ X s := by
  have hc := twoShift_even_difference_eq hp hn hi he s
  rw [twoShift_even_difference_profile χ hs, twoShift_difference_eq_tail χ hx hpass] at hc
  linarith only [hc]

/-- Combining the four fixed-frequency contours removes the unshifted
Euler term. The conductor, poles, zeta correction and signed Euler tail
remain separate for the final two-shift estimate. -/
theorem twoShift_cosine_combination {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) {X : ℝ} (hX : 85264 ≤ X) (hRH : RiemannHypothesis)
    (ha :
      ∀ s,
        0 ≤ s → twoShiftContourValue a s = twoShiftXiContourValue s + twoShiftTailDifference a X s)
    (hb :
      ∀ s,
        0 ≤ s → twoShiftContourValue b s = twoShiftXiContourValue s + twoShiftTailDifference b X s)
    (hc :
      ∀ s,
        0 ≤ s →
          twoShiftContourValue c s = twoShiftXiContourValue s + twoShiftTailDifference c X s) :
    let W := fun s ↦ twoShiftContourValue a s + twoShiftContourValue b s + twoShiftContourValue c s
    let B := fun s : ℝ ↦ twoShiftSymmetricProfile (Real.exp s)⁻¹
    (W (14 / 5) - W 3) / 2 - (W 0 - W (1 / 5)) / 4 =
      2 * Real.log n * ((B (14 / 5) - B 3) / 2 - (B 0 - B (1 / 5)) / 4) +
          (twoShiftPoleConstant + 3 / 5000) -
        3 * twoShiftZetaCosineCorrection -
        ∑' k : { m : ℕ // ⌊X⌋₊ < m },
          (3 - ((a k.val).re + (b k.val).re + (c k.val).re)) *
            (ArithmeticFunction.vonMangoldt k.val / (k.val : ℝ) ^ (38 / 25 : ℝ) *
              twoShiftEulerPoly (Real.log k.val)) := by
  intro W B
  have hW (s : ℝ) (hs : 0 ≤ s) :
    W s =
      3 * twoShiftXiContourValue s + 2 * Real.log n * B s -
          6 * ((51 / 50 : ℝ) ^ 5 / ((51 / 50) ^ 2 - 1 / 4) ^ 3) * Real.cosh (s / 2) +
        twoShiftCosineTail a b c X s := by
    dsimp only [W, B]
    linarith only [ha s hs, hb s hs, hc s hs, twoShift_three_cosine_tail hn a b c X s]
  have hh := twoShift_cosine_tail_combination a b c hX
  have hz := twoShift_zeta_eq_contours hRH
  dsimp only at hh
  rw [hW (14 / 5) (by norm_num only), hW 3 (by norm_num only), hW 0 (le_refl _),
    hW (1 / 5) (by norm_num only)]
  unfold twoShiftPoleConstant
  norm_num only [Real.cosh_zero] at *
  linarith only [hh, hz]

/-- Retain the cutoff-dependent reflected majorant when comparing the two
shifted residue sums. The common zeta zeros cost at most 0.00024. -/
theorem twoShift_residue_signed_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (a : DirichletCharacter ℂ (p * q)) (b : DirichletCharacter ℂ (p * r))
    (c : DirichletCharacter ℂ (q * r)) (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (ha : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → a k = 1) (hb : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → b k = 1)
    (hc : ∀ k : ℕ, k.Prime → (k : ℝ) ≤ X → c k = 1) :
    let B := X * Real.exp (-(14 / 5))
    let T := X * Real.exp (-3)
    let R := fun y ↦ twoShiftResidueValue a y + twoShiftResidueValue b y + twoShiftResidueValue c y
    (twoShiftRealMain n B - twoShiftRealMain n T) / 2 - 24 / 100000 -
        2 * ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) * twoShiftReflectedTail X) ≤
      (R B - R T) / 2 := by
  intro B T R
  have hx : 0 < X := by linarith only [hX]
  have hB : 0 < B := mul_pos hx (Real.exp_pos _)
  have hT : 0 < T := mul_pos hx (Real.exp_pos _)
  have hT₁ : 1 ≤ T := by
    dsimp only [T]
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 3
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h
    linarith only [h, hX]
  have e₁ := (twoShift_triple_residue_error hn a b c hx.le hB ht ha hb hc).1
  have e₂ := (twoShift_triple_residue_error hn a b c hx.le hT ht ha hb hc).2
  have htail :
    (∑' k : { m : ℕ // ⌊X⌋₊ < m }, twoShiftDualWeight T k.val) =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5))) * twoShiftReflectedTail X := by
    dsimp only [T]
    rw [tsum_congr (fun k : { m : ℕ // ⌊X⌋₊ < m } ↦ twoShift_dual_density hx hT₁ k.val),
      tsum_mul_left, mul_assoc]
    rfl
  rw [htail] at e₂
  rw [twoShift_triple_main_eq n hB] at e₁
  rw [twoShift_triple_main_eq n hT] at e₂
  have hz := (Complex.abs_re_le_norm _).trans (twoShift_zeta_sum_diff_bound hRH hB hT)
  rw [Complex.sub_re] at hz
  dsimp only [R]
  linarith only [e₁, e₂, (abs_le.mp hz).1]

/-- At radius r and shift s beyond 14/5, the real main term retains the
density and the two half-poles with their exact exponential factors. -/
private theorem twoShift_main_at_shift (n : ℕ) {r s : ℝ} (hr : 0 < r) (hs : s ≤ 2 * Real.log r) :
    twoShiftRealMain n (r ^ 2 * Real.exp (-(14 / 5 + s))) =
      2 * Real.log n *
          ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (2 * Real.log r - s)) *
            (2 * Real.log r - s) ^ 5) -
        3 *
          ((51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6 * Real.exp (s / 2) / r +
            (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6 * Real.exp (-(s / 2)) * r) := by
  let y := r ^ 2 * Real.exp (-(14 / 5 + s))
  have hy : 0 < y := mul_pos (sq_pos_of_pos hr) (Real.exp_pos _)
  have hlog : Real.log y = 2 * Real.log r - (14 / 5 + s) := by
    dsimp only [y]
    rw [Real.log_mul (sq_pos_of_pos hr).ne' (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    norm_num only [Nat.cast_ofNat]
    ring
  have hprof :
    Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) y⁻¹ =
      (51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(51 / 50) * (2 * Real.log r - s)) *
        (2 * Real.log r - s) ^ 5 := by
    unfold Analysis.rationalPoleProfile
    rw [Real.log_inv, hlog, ite_eq_left ⟨inv_pos.mpr hy, by linarith only [hs]⟩]
    norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
    rw [show
        (14 / 5 - -(2 * Real.log r - (14 / 5 + s))) / (50 / 51 : ℝ) =
          (51 / 50) * (2 * Real.log r - s)
        by ring,
      neg_mul]
    ring
  have hplus : y ^ (1 / 2 : ℝ) = r * (Real.exp (-(7 / 5)) * Real.exp (-(s / 2))) := by
    rw [Real.rpow_def_of_pos hy, hlog,
      show (2 * Real.log r - (14 / 5 + s)) * (1 / 2 : ℝ) = Real.log r + (-(7 / 5) + -(s / 2)) by
        ring,
      Real.exp_add, Real.exp_log hr, Real.exp_add]
  have hminus : y ^ (-1 / 2 : ℝ) = (Real.exp (7 / 5) * Real.exp (s / 2)) / r := by
    rw [Real.rpow_def_of_pos hy, hlog,
      show (2 * Real.log r - (14 / 5 + s)) * (-1 / 2 : ℝ) = (7 / 5 + s / 2) + -Real.log r by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hr]
    rfl
  have hcancel : Real.exp (7 / 5 : ℝ) * Real.exp (-(7 / 5)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hneg :
    (50 / 51) * Real.exp (-(7 / 5)) / (1 - 25 / 51) ^ 6 *
        ((Real.exp (7 / 5) * Real.exp (s / 2)) / r) =
      (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6 * Real.exp (s / 2) / r := by
    calc
      _ =
          (51 / 50 : ℝ) ^ 5 / (13 / 25) ^ 6 * (Real.exp (7 / 5) * Real.exp (-(7 / 5))) *
              Real.exp (s / 2) /
            r :=
        by ring
      _ = _ := by rw [hcancel, mul_one]
  have hpos :
    (50 / 51) * Real.exp (7 / 5) / (1 + 25 / 51) ^ 6 *
        (r * (Real.exp (-(7 / 5)) * Real.exp (-(s / 2)))) =
      (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6 * Real.exp (-(s / 2)) * r := by
    calc
      _ =
          (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6 * (Real.exp (7 / 5) * Real.exp (-(7 / 5))) *
            Real.exp (-(s / 2)) *
            r :=
        by ring
      _ = _ := by rw [hcancel, mul_one]
  change twoShiftRealMain n y = _
  unfold twoShiftRealMain
  rw [hprof, hplus, hminus, hneg, hpos]

/-- At the quarter-square cutoff the half-weighted difference of the real
main terms is the conductor and reciprocal correction, together with the
linear loss from the positive half-pole. -/
theorem twoShift_real_main_difference (n : ℕ) {r : ℝ} (hr : 0 < r) (hu : 1 / 5 ≤ 2 * Real.log r)
    (hn : Real.log n = 2 * r) :
    (twoShiftRealMain n (r ^ 2 * Real.exp (-(14 / 5))) -
          twoShiftRealMain n (r ^ 2 * Real.exp (-3))) /
        2 =
      twoShiftConductor (2 * Real.log r) + twoShiftReciprocalCoeff / r -
        (3 * (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6 * (1 - Real.exp (-(1 / 10)))) / 2 * r := by
  have h₀ := twoShift_main_at_shift n hr ((by norm_num only : (0 : ℝ) ≤ 1 / 5).trans hu)
  have h₁ := twoShift_main_at_shift n hr hu
  norm_num only [add_zero, sub_zero, zero_div, neg_zero, Real.exp_zero, div_div, mul_one] at h₀
  rw [show -(14 / 5 + 1 / 5 : ℝ) = -3 by norm_num only,
    show (1 / 5 : ℝ) / 2 = 1 / 10 by norm_num only] at h₁
  rw [h₀, h₁, hn]
  unfold twoShiftConductor twoShiftReciprocalCoeff
  have hshift :
    Real.exp (-(51 / 50 : ℝ) * (2 * Real.log r - 1 / 5)) =
      Real.exp (-(51 / 50) * (2 * Real.log r)) * Real.exp ((51 / 50) * (1 / 5)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscale :
    r * Real.exp (-(51 / 50 : ℝ) * (2 * Real.log r)) =
      Real.exp (-(13 / 25) * (2 * Real.log r)) := by
    calc
      _ = Real.exp (Real.log r) * Real.exp (-(51 / 50) * (2 * Real.log r)) := by
        rw [Real.exp_log hr]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [hshift]
  linear_combination (norm := ring)
    ((51 / 50 : ℝ) ^ 5 / 60 *
        ((2 * Real.log r) ^ 5 - Real.exp ((51 / 50) * (1 / 5)) * (2 * Real.log r - 1 / 5) ^ 5)) *
      hscale

end PseudoPrime.PrimeTestBounds.MillerRabin
