/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSharpLeftMomentBounds
public import PseudoPrime.Analysis.GammaNegativeConductor
public import PseudoPrime.Analysis.ReflectedEulerGammaInversion

/-!
# Signed conductor splitting of the actual Gamma left integral

The constant reflected conductor term is evaluated before taking norms of the remainder.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The actual Gamma weight on the fixed completed left line. The Gamma argument has
real part -1/16 and the scale exponent has real part -9/16. This agrees with the existing
Gamma Mellin kernel after its half shift. -/
noncomputable def gammaSignedLeftWeight (x t : ℝ) : ℂ :=
  Complex.Gamma (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) *
    (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)

/-- The actual negative completed-logarithmic-derivative left integrand, expressed with
the unshifted Gamma argument. It is split into the exact conductor term and a reflected
right-line remainder below. -/
noncomputable def gammaSignedLeftIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) : ℂ :=
  -logDeriv χ.completedLFunction (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) * gammaSignedLeftWeight x t

/-- The normalized actual completed left integral, on the same line as the previous
absolute-value estimates. The new bound controls its real part, retaining the conductor sign. -/
noncomputable def gammaSignedLeftIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, gammaSignedLeftIntegrand χ x t

/-- A positive real base to the complex negative half power is the inverse real square
root. This factors the half shift out of the actual left weight. -/
theorem gamma_signed_left_cpow_neg_half {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) = (Real.sqrt x : ℂ)⁻¹ := by
  rw [← Complex.ofReal_cpow hx.le]
  rw [neg_div, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]

/-- Factor the actual left weight into the negative-strip Gamma inversion weight and
the inverse square root of the scale. No absolute-value estimate is used. -/
theorem gammaSignedLeftWeight_eq_factored {x : ℝ} (hx : 0 < x) (t : ℝ) :
    gammaSignedLeftWeight x t =
      (Real.sqrt x : ℂ)⁻¹ *
        (Complex.Gamma (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) *
          (x : ℂ) ^ (((-1 / 16 : ℝ) : ℂ) + t * Complex.I)) := by
  dsimp only [gammaSignedLeftWeight]
  have he :
    (((-9 / 16 : ℝ) : ℂ) + t * Complex.I) =
      ((-1 / 2 : ℝ) : ℂ) + (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    gamma_signed_left_cpow_neg_half hx]
  ring

/-- The actual left Gamma weight is absolutely integrable for positive scale.
Gamma is integrable on the negative strip, and the power factor has constant norm. -/
theorem integrable_gammaSignedLeftWeight {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (gammaSignedLeftWeight x) := by
  have hΓ :=
    PseudoPrime.Analysis.integrable_Gamma_negative_vertical (c := -1 / 16) (by norm_num only)
      (by norm_num only)
  have hp : Continuous (fun t : ℝ ↦ (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)) := by
    exact
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hb : ∀ t : ℝ, ‖(x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + t * Complex.I)‖ ≤ x ^ (-9 / 16 : ℝ) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, le_refl]
  have h := hΓ.bdd_mul hp.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  exact
    h.congr
      (Filter.Eventually.of_forall
        (fun t ↦ by
          dsimp only [gammaSignedLeftWeight]
          exact mul_comm _ _))

/-- The normalized weight integral is the real conductor term with coefficient one.
Factor the half shift and apply the proved negative Gamma inversion. -/
theorem integral_gammaSignedLeftWeight {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, gammaSignedLeftWeight x t) =
      (PseudoPrime.Analysis.gammaNegativeConductorTerm 1 x : ℂ) := by
  simp only [gammaSignedLeftWeight_eq_factored hx, MeasureTheory.integral_const_mul]
  have h :=
    PseudoPrime.Analysis.negative_conductor_vertical_integral_eq (c := -1 / 16) (by norm_num only)
      (by norm_num only) hx 1
  simpa only [Complex.real_smul, Complex.ofReal_one, one_div, mul_assoc, mul_left_comm,
    mul_comm] using h

/-- The unshifted integrand agrees with the existing Gamma Mellin left-line integrand.
Identify the two contour coordinates and the kernel's defining Gamma shift. -/
theorem gammaSignedLeftIntegrand_eq_original {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x t : ℝ) :
    gammaSignedLeftIntegrand χ x t =
      -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
        (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  change
    -logDeriv χ.completedLFunction _ * _ = -logDeriv χ.completedLFunction _ * (Complex.Gamma _ * _)
  dsimp only [gammaSignedLeftWeight]
  have he :
    (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) = (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, mul_comm (t : ℂ) Complex.I]

/-- The actual signed left integrand is integrable for primitive nonprincipal data.
Transport the existing completed-line integrability through the exact coordinate identity. -/
theorem integrable_gammaSignedLeftIntegrand {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable (gammaSignedLeftIntegrand χ x) := by
  have h :=
    MellinKernel.integrable_completed_left_line gammaMellinKernel hp hne hinv
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) hx
  exact
    h.congr
      (Filter.Eventually.of_forall (fun t ↦ (gammaSignedLeftIntegrand_eq_original χ x t).symm))

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Reflect the completed derivative before taking norms: the actual left integrand
equals the conductor coefficient plus the inverse character's right-line derivative,
times the common Gamma weight. This identity holds at every real height. -/
theorem gammaSignedLeftIntegrand_reflection {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (x t : ℝ) :
    gammaSignedLeftIntegrand χ x t =
      (Complex.log (q : ℂ) +
          logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))) *
        gammaSignedLeftWeight x t := by
  let r : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
  have hr : 1 ≤ r.re := by
    simp only [r, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only
  have h :=
    completedLFunction_logDeriv_functionalEquation_at hp hne
      (completedLFunction_ne_zero_of_one_le_re hinv hr)
  have he : 1 - r = ((-1 / 16 : ℝ) : ℂ) + t * Complex.I := by
    dsimp only [r]
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he] at h
  exact congrArg (fun z : ℂ ↦ z * gammaSignedLeftWeight x t) h

/-- The actual left integrand minus its conductor component is integrable.
Use existing actual left-line integrability and the separately integrable Gamma weight. -/
theorem integrable_gammaSignedLeftRemainder {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t ↦
        gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t) := by
  simpa only [Pi.sub_def] using
    (integrable_gammaSignedLeftIntegrand hp hne hinv hx).sub
      ((integrable_gammaSignedLeftWeight hx).const_mul (Complex.log (q : ℂ)))

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- After subtracting the exact conductor component, the pointwise envelope uses
constant twenty-eight and no log q. Reflect before taking norms, then combine the
two certified Gamma moment envelopes. -/
theorem gammaSignedLeftRemainder_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t‖ ≤
      x ^ (-9 / 16 : ℝ) *
        (28 * PseudoPrime.Analysis.gammaRefinedZeroEnvelope t +
          PseudoPrime.Analysis.gammaRefinedFirstEnvelope t) := by
  rw [gammaSignedLeftIntegrand_reflection hp hne hinv, add_mul, add_sub_cancel_left]
  have hd := norm_logDeriv_completed_seventeen_sixteenths_le_refined hinv (-t)
  rw [abs_neg] at hd
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
  have he := add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num only : (0 : ℝ) ≤ 28)) h1
  have hb :
    ‖logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))‖ *
        ‖Complex.Gamma z‖ ≤
      28 * PseudoPrime.Analysis.gammaRefinedZeroEnvelope t +
        PseudoPrime.Analysis.gammaRefinedFirstEnvelope t := by
    nlinarith only [hdg, he]
  dsimp only [gammaSignedLeftWeight]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hr : ((((-9 / 16 : ℝ) : ℂ) + t * Complex.I)).re = -9 / 16 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [hr, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx.le _)).trans_eq (mul_comm _ _)

/-- The normalized actual reflected remainder has norm at most 43 x^(-9/16).
Integrate the conductor-free pointwise bound using the certified moments 3/2 and one. -/
theorem norm_gammaSignedLeftRemainder_integral_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t)‖ ≤
      43 * x ^ (-9 / 16 : ℝ) := by
  let F := fun t ↦ gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t
  have hfi := integrable_gammaSignedLeftRemainder hp hne hinv hx
  let E := fun t : ℝ ↦
    x ^ (-9 / 16 : ℝ) *
      (28 * PseudoPrime.Analysis.gammaRefinedZeroEnvelope t +
        PseudoPrime.Analysis.gammaRefinedFirstEnvelope t)
  have hEi : MeasureTheory.Integrable E :=
    ((PseudoPrime.Analysis.gammaRefinedZeroEnvelope_integrable.const_mul 28).add
          PseudoPrime.Analysis.gammaRefinedFirstEnvelope_integrable).const_mul
      _
  have hb :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hEi
        (fun t ↦ gammaSignedLeftRemainder_bound hp hne hinv hx t))
  have hm := gamma_sharp_left_envelope_normalized_le (C := 28) (by norm_num only)
  norm_num only at hm
  have hpi : 0 ≤ (1 / (2 * Real.pi) : ℝ) :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le)
  have hmul := mul_le_mul_of_nonneg_left hb hpi
  dsimp only [E] at hmul
  rw [MeasureTheory.integral_const_mul] at hmul
  have he := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hx.le (-9 / 16))
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpi]
  nlinarith only [hmul, he]

/-- The normalized signed left integral agrees with the original public contour expression.
The coordinate identity is pointwise, so no convergence premise is needed for this rewrite. -/
theorem gammaSignedLeftIntegral_eq_original {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) :
    gammaSignedLeftIntegral χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  simp only [gammaSignedLeftIntegral, gammaSignedLeftIntegrand_eq_original]

/-- Split the actual normalized completed left integral into its exactly evaluated
signed conductor contribution and the integrable reflected remainder. Integral linearity
is justified by both actual integrability proofs. -/
theorem gammaSignedLeftIntegral_eq_conductor_add_remainder {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    gammaSignedLeftIntegral χ x =
      (PseudoPrime.Analysis.gammaNegativeConductorTerm (Real.log q) x : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t) := by
  have h :=
    MeasureTheory.integral_sub (integrable_gammaSignedLeftIntegrand hp hne hinv hx)
      ((integrable_gammaSignedLeftWeight hx).const_mul (Complex.log (q : ℂ)))
  rw [MeasureTheory.integral_const_mul] at h
  have hw := integral_gammaSignedLeftWeight hx
  have he :
    gammaSignedLeftIntegral χ x =
      Complex.log (q : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, gammaSignedLeftWeight x t) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t) := by
    rw [h]
    dsimp only [gammaSignedLeftIntegral]
    ring
  rw [he, hw, ← Complex.natCast_log]
  simp only [PseudoPrime.Analysis.gammaNegativeConductorTerm, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one]
  ring

/-- The real part of the actual completed left integral is at most its nonpositive
exact conductor term plus 43 x^(-9/16). Retain the signed conductor integral and take
norms only of the reflected remainder. No RH hypothesis is needed. -/
theorem re_gammaSignedLeftIntegral_le_conductor_add {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (gammaSignedLeftIntegral χ x).re ≤
      PseudoPrime.Analysis.gammaNegativeConductorTerm (Real.log q) x + 43 * x ^ (-9 / 16 : ℝ) := by
  rw [gammaSignedLeftIntegral_eq_conductor_add_remainder hp hne hinv hx, Complex.add_re,
    Complex.ofReal_re]
  have hr :=
    Complex.re_le_norm
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t))
  have hn := norm_gammaSignedLeftRemainder_integral_le hp hne hinv hx
  linarith only [hr, hn]

/-- For positive scale and primitive nonprincipal data, the actual completed left
integral has real part at most 43 x^(-9/16), with no positive log-conductor allowance.
Discard only the already nonpositive exact conductor contribution. -/
theorem re_gammaSignedLeftIntegral_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    (gammaSignedLeftIntegral χ x).re ≤ 43 * x ^ (-9 / 16 : ℝ) := by
  have h := re_gammaSignedLeftIntegral_le_conductor_add hp hne hinv hx
  have hc := PseudoPrime.Analysis.gammaNegativeConductorTerm_nonpos (Real.log_natCast_nonneg q) hx
  linarith only [h, hc]

end PseudoPrime.LLS.PaperStatements
