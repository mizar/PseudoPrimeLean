/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaCellPrimitive
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundThetaMainPart
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogFactor
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Normalized critical-line signs -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- At positive real part away from the pole, the xi factorization separates
the elementary polynomial and the Euler-normalized Gamma exponential. This
form is used to compare signs on the critical line. -/
private theorem xi_euler_factor {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s =
      (1 / 2 : ℂ) * s * (s - 1) *
        Complex.exp (Gamma.logGammaSeries (s / 2) - (s / 2) * (Real.log Real.pi : ℂ)) *
        riemannZeta s := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [riemannXi_eq_exp_factor hs hs1]
  have he :
    xiLogFactor s =
      Complex.log s + Complex.log (s - 1) +
        (Gamma.logGammaSeries (s / 2) - (s / 2) * (Real.log Real.pi : ℂ)) := by
    unfold xiLogFactor
    ring
  rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_log hs0, Complex.exp_log hs10]
  ring

/-- On the critical line, the imaginary part of the Euler-normalized xi
exponent is the existing Gamma phase. The identity keeps the analytic
logarithm normalization used in the zero-count argument. -/
private theorem critical_factor_im (t : ℝ) :
    let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
    (Gamma.logGammaSeries (s / 2) - (s / 2) * (Real.log Real.pi : ℂ)).im =
      RiemannZeta.backlundTheta t := by
  dsimp only [RiemannZeta.backlundTheta]
  have hs :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 =
      ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  simp only [hs, Complex.sub_im, Complex.mul_im, Complex.ofReal_im, mul_zero, zero_add,
    Complex.ofReal_re, Complex.add_im, Complex.I_im, Complex.I_re, mul_one, add_zero]

/-- The polynomial factor `s(s - 1)` on the critical line is the negative
real number `-(t² + 1/4)`. This removes its phase from the xi factor. -/
private theorem critical_quadratic (t : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1) =
      (-((t ^ 2 + 1 / 4) : ℝ) : ℂ) := by
  simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_one]
  linear_combination (t : ℂ) ^ 2 * Complex.I_sq

/-- A critical-line xi factor with exponent `u` separates into a negative
real amplitude and a rotation through the imaginary part of `u`. -/
private theorem critical_exp_factor (t : ℝ) (u z w : ℂ) (hu : u.im = RiemannZeta.backlundTheta t)
    (hw :
      w =
        (1 / 2 : ℂ) * (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1) *
          Complex.exp u *
          z) :
    w =
      (-((t ^ 2 + 1 / 4) / 2 * Real.exp u.re) : ℂ) *
        (Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) * z) := by
  have he : Complex.exp u = (Real.exp u.re : ℂ) * Complex.exp ((u.im : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im u]
    rw [Complex.exp_add, Complex.ofReal_exp]
  rw [hw, he, hu]
  calc
    _ =
        (1 / 2 : ℂ) *
          ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
            ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)) *
          ((Real.exp u.re : ℂ) * Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I)) *
          z :=
      by ring
    _ = _ := by
      rw [critical_quadratic]
      ring_nf
      simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.ofReal_one]
      ring

/-- On the critical line, xi is a negative positive real amplitude times
zeta rotated by the exact Euler-normalized Gamma phase. No numerical value of
the Gamma amplitude is needed for this factorization. -/
private theorem xi_critical_factor (t : ℝ) :
    ∃ a : ℝ,
      0 < a ∧
        riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
          (-a : ℂ) *
            (Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) *
              riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let u : ℂ := Gamma.logGammaSeries (s / 2) - (s / 2) * (Real.log Real.pi : ℂ)
  have hs : s.re = 1 / 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hs0 : 0 < s.re := by linarith only [hs]
  have hs1 : s ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hs
    norm_num only at hs
  have hu : u.im = RiemannZeta.backlundTheta t := critical_factor_im t
  have hw := xi_euler_factor hs0 hs1
  refine ⟨(t ^ 2 + 1 / 4) / 2 * Real.exp u.re, ?_, ?_⟩
  · have hp : 0 < t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
    exact mul_pos (div_pos hp (by norm_num only)) (Real.exp_pos _)
  · simpa only [s, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_one] using
      critical_exp_factor t u (riemannZeta s) (riemannXi s) hu hw

/-- Multiplying a complex value by a negative real amplitude preserves its
zero imaginary part and scales its real part by that amplitude. -/
private theorem negative_factor_real (a : ℝ) (ha : 0 < a) (w z : ℂ) (hw : w = (-a : ℂ) * z)
    (hi : w.im = 0) : z.im = 0 ∧ w.re = -a * z.re := by
  rw [hw] at hi ⊢
  simp only [Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, add_zero, sub_zero] at hi ⊢
  constructor
  · exact (mul_eq_zero.mp hi).resolve_left (neg_ne_zero.mpr ha.ne')
  · exact True.intro

/-- The exact Gamma-phase rotation of zeta is real on the critical line,
and its real part has the opposite sign to xi through a positive factor. -/
private theorem xi_rotated_re (t : ℝ) :
    ∃ a : ℝ,
      0 < a ∧
        (Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) *
              riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im =
          0 ∧
        (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re =
          -a *
            (Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) *
                riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨a, ha, hf⟩ := xi_critical_factor t
  have hs : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) : ℂ).re = 1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hi := riemannXi_critical_im_eq_zero hs
  exact ⟨a, ha, negative_factor_real a ha _ _ hf hi⟩

/-- The imaginary finite Gamma identity at `1/4 + it/2` holds at every real
height and natural cutoff. It follows by telescoping the unit-cell formula. -/
private theorem gamma_finite_im (t : ℝ) (N : ℕ) :
    let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
    (AnalyticNumberTheory.Gamma.backlundGammaPartial z N -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z -
          ∫ u in (0 : ℝ)..(N : ℝ), RiemannZeta.backlundGammaComplexKernel (1 / 4) (t / 2) u).im =
      (t / 2) * ((harmonic N : ℝ) - Real.eulerMascheroniConstant) -
        (AnalyticNumberTheory.Gamma.backlundStirlingMain ((N : ℂ) + z)).im := by
  let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
  have hz : z.im = t / 2 := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hi := RiemannZeta.gamma_complex_integral_nat (a := 1 / 4) (y := t / 2) (by norm_num only) N
  change _ = _ at hi
  change
    (AnalyticNumberTheory.Gamma.backlundGammaPartial z N -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z -
          ∫ u in (0 : ℝ)..(N : ℝ), RiemannZeta.backlundGammaComplexKernel (1 / 4) (t / 2) u).im =
      (t / 2) * ((harmonic N : ℝ) - Real.eulerMascheroniConstant) -
        (AnalyticNumberTheory.Gamma.backlundStirlingMain ((N : ℂ) + z)).im
  rw [hi]
  simp only [Complex.sub_im, Complex.im_sum, AnalyticNumberTheory.Gamma.gamma_partial_im, hz]
  have hcomm : (N : ℂ) + z = z + N := add_comm _ _
  rw [hcomm]
  ring

/-- At every real height, the imaginary Gamma remainder equals the negative
integral of the real Euler–Maclaurin kernel. This specializes the finite-cell
identity and its limit without imposing a lower bound on the height. -/
private theorem gamma_remainder_integral (t : ℝ) :
    RiemannZeta.backlundGammaRemainder t =
      -(∫ x in Set.Ioi (0 : ℝ),
          RiemannZeta.backlundGammaWeight x *
            RiemannZeta.backlundGammaKernel (1 / 4) (t / 2) x) := by
  let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I
  have h :=
    RiemannZeta.gamma_remainder_im_of_finite (a := 1 / 4) (y := t / 2) (by norm_num only)
      (gamma_finite_im t)
  change
    (AnalyticNumberTheory.Gamma.logGammaSeries z -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z -
          ∫ u in Set.Ioi (0 : ℝ), RiemannZeta.backlundGammaComplexKernel (1 / 4) (t / 2) u).im =
      0 at h
  rw [Complex.sub_im, RiemannZeta.backlundGammaComplexKernel_integral_im (by norm_num only)] at h
  change
    (AnalyticNumberTheory.Gamma.logGammaSeries z -
          AnalyticNumberTheory.Gamma.backlundStirlingMain z).im =
      _
  linarith only [h]

/-- For every positive height, the Euler-normalized Gamma phase differs from
its elementary main term by at most `1 / (4 * t)`. The proof bounds the signed
Gamma remainder integral and retains the existing logarithm normalization. -/
theorem gamma_phase_error {t : ℝ} (ht : 0 < t) :
    |RiemannZeta.backlundTheta t - RiemannZeta.backlundThetaMain t| ≤ 1 / (4 * t) := by
  have h := RiemannZeta.backlundGammaWeight_integral_height ht
  apply RiemannZeta.backlundTheta_error_of_signed_remainder ht
  · rw [gamma_remainder_integral]
    linarith only [h.2.2]
  · rw [gamma_remainder_integral]
    linarith only [h.2.1]

/-- At heights at least 14, the cosine of the difference between the
elementary phase and the Euler-normalized Gamma phase is positive. This
allows the two rotated critical-line zeta values to have the same sign. -/
theorem phase_difference_cos_pos {t : ℝ} (ht : 14 ≤ t) :
    0 < Real.cos (RiemannZeta.backlundThetaMain t - RiemannZeta.backlundTheta t) := by
  have ht0 : 0 < t := by linarith only [ht]
  have h := gamma_phase_error ht0
  have hb : 1 / (4 * t) ≤ (1 / 56 : ℝ) := by
    apply (div_le_iff₀ (mul_pos (by norm_num only) ht0)).2
    linarith only [ht]
  have hp : (1 / 56 : ℝ) < Real.pi / 2 := by
    have hpi := Real.pi_gt_three
    linarith only [hpi]
  apply Real.cos_pos_of_mem_Ioo
  have hh := abs_le.mp h
  constructor <;> linarith only [hh.1, hh.2, hb, hp]

/-- If rotation by the exact Gamma phase makes a complex value real, rotating
it by another real phase multiplies its real part by the cosine of the phase
difference. This algebraic identity preserves the sign when the cosine is positive. -/
private theorem rotated_re (a b : ℝ) (z : ℂ) (hz : (Complex.exp ((b : ℂ) * Complex.I) * z).im = 0) :
    (Complex.exp ((a : ℂ) * Complex.I) * z).re =
      Real.cos (a - b) * (Complex.exp ((b : ℂ) * Complex.I) * z).re := by
  have he :
    Complex.exp ((a : ℂ) * Complex.I) =
      Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_sub]
    ring
  rw [he, mul_assoc, Complex.mul_re, Complex.exp_ofReal_mul_I_re, hz, mul_zero, sub_zero]

/-- The elementary-phase rotation and exact Gamma-phase rotation have the
same sign at heights at least 14, provided the latter is real. The exact
phase error gives the strict positivity of the cosine factor. -/
theorem normalized_rotation_sign {t : ℝ} (ht : 14 ≤ t) (z : ℂ)
    (hz : (Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) * z).im = 0) :
    0 < (Complex.exp ((RiemannZeta.backlundThetaMain t : ℂ) * Complex.I) * z).re ↔
      0 < (Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) * z).re := by
  rw [rotated_re _ _ z hz, mul_pos_iff_of_pos_left (phase_difference_cos_pos ht)]

/-- The real part of zeta on the critical line after rotation by the
elementary Gamma phase. Its sign can be certified from a finite approximation
without numerically evaluating the small positive xi amplitude. -/
@[expose]
noncomputable def normalizedZeta (t : ℝ) : ℝ :=
  (Complex.exp ((RiemannZeta.backlundThetaMain t : ℂ) * Complex.I) *
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re

/-- At heights at least 14, the normalized zeta value and the real critical
xi value have opposite strict signs. The exact Gamma rotation is real, and
the cosine of the difference from the elementary phase is positive. -/
theorem normalized_zeta_xi_sign {t : ℝ} (ht : 14 ≤ t) :
    (0 < normalizedZeta t → (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0) ∧
      (normalizedZeta t < 0 → 0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re) := by
  obtain ⟨a, ha, hz, hx⟩ := xi_rotated_re t
  have hc := phase_difference_cos_pos ht
  have hy :=
    rotated_re (RiemannZeta.backlundThetaMain t) (RiemannZeta.backlundTheta t)
      (riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) hz
  change normalizedZeta t = _ at hy
  constructor
  · intro h
    rw [hy] at h
    have hp := (mul_pos_iff_of_pos_left hc).mp h
    rw [hx]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hp
  · intro h
    rw [hy] at h
    have hp :
      0 <
        Real.cos (RiemannZeta.backlundThetaMain t - RiemannZeta.backlundTheta t) *
          (-(Complex.exp ((RiemannZeta.backlundTheta t : ℂ) * Complex.I) *
                riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re) := by
      linarith only [h]
    have hn := (mul_pos_iff_of_pos_left hc).mp hp
    rw [hx]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos ha) (neg_pos.mp hn)

end PseudoPrime.AnalyticNumberTheory.RiemannXi
