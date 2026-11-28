/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness
public import PseudoPrime.LLS.PaperStatements.ResolventLaplaceWeights
public import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedDigamma
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaCoefficients
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaCell

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness
import all PseudoPrime.LLS.PaperStatements.ShiftedPoleArithmetic

/-! # Inverse profiles for the high Gaussian gamma contour -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- In logarithmic coordinates the high-kernel inverse transform is the
exponentially damped physical polynomial for nonnegative height and zero
for negative height, on both contour lines. -/
theorem high_gaussian_inverse_log (K : HighGaussianKernel) {c : ℝ} (hc : -(9 / 16 : ℝ) ≤ c)
    (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (z : ℝ) :
    Analysis.inverseMellin (highGaussianSquare K) c (Real.exp (5 - z)) =
      if 0 ≤ z then ((Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z : ℝ) : ℂ) else 0 := by
  by_cases hz : 0 ≤ z
  · rw [ite_eq_left hz, high_gaussian_square_inverse_sum K hc hc' hne (Real.exp_pos _)]
    have h :=
      LLS.PaperStatements.shiftedPole_transform_sum (Finset.range (2 * K.degree + 1)) K.logPower
        (fun j ↦ (K.expandedCoeff j : ℂ)) (fun _ ↦ (by decide : 1 ≤ 3).trans (Nat.le_add_left _ _))
        (high_gaussian_pole_gt K) (Real.exp_pos (5 - z)) (Real.exp_le_exp.mpr (sub_le_self _ hz))
    rw [Real.log_exp, sub_sub_cancel, ← Real.exp_add] at h
    rw [h, show (5 - z : ℝ) + -5 = -z by ring, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      mul_comm (-z), mul_neg, ← neg_mul, Complex.ofReal_mul, high_real_profile_eval]
    rfl
  · rw [ite_eq_right hz]
    exact
      high_gaussian_square_inverse_zero K hc hc' hne
        (Real.exp_le_exp.mpr (by linarith only [le_of_not_ge hz]))

/-- Convert a forward reciprocal contour factor into a Laplace integral of
the inverse kernel. The shift is toward smaller logarithmic heights. -/
theorem high_gamma_forward_resolvent (F : ℂ → ℂ) {b c z : ℝ} (hb : 0 < b) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ F (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) =
        ∫ u in Set.Ioi (0 : ℝ),
          (Real.exp ((c / 2 - b) * u) : ℂ) *
            Analysis.inverseMellin F c (Real.exp (5 - (z - u / 2))) := by
  intro l W hW hiW
  rw [LLS.PaperStatements.resolvent_integral_eq_laplace_weight hb W hW hiW, ←
    MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun u ↦ ?_
  dsimp only [Analysis.inverseMellin]
  rw [mul_left_comm _ (((1 / (2 * Real.pi) : ℝ) : ℂ))]
  apply congrArg (((1 / (2 * Real.pi) : ℝ) : ℂ) * ·)
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun t ↦ ?_
  dsimp only
  have hu := Real.exp_pos (5 - (z - u / 2))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
    Real.log_exp, Complex.ofReal_exp]
  dsimp only [W, l]
  calc
    _ =
        F ((c : ℂ) + Complex.I * t) *
          Complex.exp
            (-((b : ℂ) + Complex.I * (t : ℂ) / 2) * (u : ℂ) +
              ((c : ℂ) + Complex.I * t) * ((z - 5 : ℝ) : ℂ)) :=
      by
      rw [Complex.exp_add]; ring
    _ = _ := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- The forward Laplace integral of the high kernel is supported on
the finite interval from zero to twice the logarithmic height. -/
theorem high_gamma_forward_truncate (K : HighGaussianKernel) {b c z : ℝ} (hc : -(9 / 16 : ℝ) ≤ c)
    (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    (∫ u in Set.Ioi (0 : ℝ),
        (Real.exp ((c / 2 - b) * u) : ℂ) *
          Analysis.inverseMellin (highGaussianSquare K) c (Real.exp (5 - (z - u / 2)))) =
      ∫ u in (0 : ℝ)..(2 * z),
        ((Real.exp ((c / 2 - b) * u - (K.pole : ℝ) * (z - u / 2)) * K.realProfile.eval (z - u / 2) :
            ℝ) :
          ℂ) := by
  have hz₂ : 0 ≤ 2 * z := mul_nonneg (by norm_num only) hz
  rw [intervalIntegral.integral_of_le hz₂, ← MeasureTheory.integral_indicator measurableSet_Ioi, ←
    MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun u ↦ ?_
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem hu, high_gaussian_inverse_log K hc hc' hne]
    by_cases hu₂ : u ≤ 2 * z
    · rw [Set.indicator_of_mem (show u ∈ Set.Ioc 0 (2 * z) from ⟨hu, hu₂⟩),
        ite_eq_left (by linarith only [hu₂] : 0 ≤ z - u / 2)]
      rw [← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add]
      rw [neg_mul, ← sub_eq_add_neg]
    · have hn : ¬u ∈ Set.Ioc 0 (2 * z) := fun h ↦ hu₂ h.2
      rw [Set.indicator_of_notMem hn,
        ite_eq_right (by linarith only [lt_of_not_ge hu₂] : ¬0 ≤ z - u / 2), mul_zero]
  · have hn : ¬u ∈ Set.Ioc 0 (2 * z) := fun h ↦ hu h.1
    rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hn]

/-- The forward reciprocal contour integral is a finite convolution at the
decay rate `pole + c - 2*b`. The factor two comes from the half-height shift. -/
theorem high_gamma_forward_moment (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) =
        ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
          ∫ v in (0 : ℝ)..z,
            ((Real.exp (((K.pole : ℝ) + c - 2 * b) * (z - v)) * K.realProfile.eval v : ℝ) : ℂ) := by
  intro l W hW hiW
  rw [high_gamma_forward_resolvent (highGaussianSquare K) hb hW hiW,
    high_gamma_forward_truncate K hc hc' hne hz]
  let G := fun v : ℝ ↦
    ((Real.exp (((K.pole : ℝ) + c - 2 * b) * (z - v)) * K.realProfile.eval v : ℝ) : ℂ)
  have he (u : ℝ) :
    ((Real.exp ((c / 2 - b) * u - (K.pole : ℝ) * (z - u / 2)) * K.realProfile.eval (z - u / 2) :
          ℝ) :
        ℂ) =
      (Real.exp (-(K.pole : ℝ) * z) : ℂ) * G (z - u / 2) := by
    rw [← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp only [he, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_div G (by norm_num only : (2 : ℝ) ≠ 0) z]
  have h : z - 2 * z / 2 = 0 := by ring
  rw [h, zero_div, sub_zero, Complex.real_smul, Complex.ofReal_mul]
  dsimp only [G]
  ring

/-- Convert a reflected reciprocal contour factor into a Laplace integral of
the inverse square kernel. The shift is toward larger logarithmic heights. -/
theorem high_gamma_reflect_resolvent (F : ℂ → ℂ) {b c z : ℝ} (hb : 0 < b) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ F (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) =
        ∫ u in Set.Ioi (0 : ℝ),
          (Real.exp ((-c / 2 - b) * u) : ℂ) *
            Analysis.inverseMellin F c (Real.exp (5 - (z + u / 2))) := by
  intro l W hW hiW
  let Wr := fun t : ℝ ↦ W (-t)
  have h₀ :=
    MeasureTheory.integral_neg_eq_self (fun t : ℝ ↦ (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t)
      MeasureTheory.volume
  simp only [Complex.ofReal_neg, mul_neg, neg_div, sub_neg_eq_add] at h₀
  rw [← h₀]
  change _ * (∫ t : ℝ, (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * Wr t) = _
  rw [LLS.PaperStatements.resolvent_integral_eq_laplace_weight hb Wr (hW.comp continuous_neg)
      hiW.comp_neg,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun u ↦ ?_
  dsimp only [Analysis.inverseMellin]
  have hu₀ :=
    MeasureTheory.integral_neg_eq_self
      (fun t : ℝ ↦ Complex.exp (-((b : ℂ) + Complex.I * (t : ℂ) / 2) * (u : ℂ)) * Wr t)
      MeasureTheory.volume
  simp only [Wr, neg_neg, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg] at hu₀
  rw [← hu₀]
  rw [mul_left_comm _ (((1 / (2 * Real.pi) : ℝ) : ℂ))]
  apply congrArg (((1 / (2 * Real.pi) : ℝ) : ℂ) * ·)
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun t ↦ ?_
  dsimp only
  have hu := Real.exp_pos (5 - (z + u / 2))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
    Real.log_exp, Complex.ofReal_exp]
  dsimp only [W, l]
  calc
    _ =
        F ((c : ℂ) + Complex.I * t) *
          Complex.exp
            (-((b : ℂ) - Complex.I * (t : ℂ) / 2) * (u : ℂ) +
              ((c : ℂ) + Complex.I * t) * ((z - 5 : ℝ) : ℂ)) :=
      by
      rw [Complex.exp_add]; ring
    _ = _ := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- At nonnegative height the reflected reciprocal integral becomes a signed
Laplace tail of the polynomial, since the shifted height stays in the support. -/
theorem high_gamma_reflect_moment (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) =
        ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
          ∫ v in Set.Ioi (0 : ℝ),
            ((Real.exp (-((K.pole : ℝ) + c + 2 * b) * v) * K.realProfile.eval (z + v) : ℝ) :
              ℂ) := by
  intro l W hW hiW
  rw [high_gamma_reflect_resolvent (highGaussianSquare K) hb hW hiW]
  let G := fun v : ℝ ↦
    ((Real.exp (-((K.pole : ℝ) + c + 2 * b) * v) * K.realProfile.eval (z + v) : ℝ) : ℂ)
  have he (u : ℝ) (hu : u ∈ Set.Ioi (0 : ℝ)) :
    (Real.exp ((-c / 2 - b) * u) : ℂ) *
        Analysis.inverseMellin (highGaussianSquare K) c (Real.exp (5 - (z + u / 2))) =
      (Real.exp (-(K.pole : ℝ) * z) : ℂ) * G ((1 / 2) * u) := by
    rw [high_gaussian_inverse_log K hc hc' hne,
      ite_eq_left (add_nonneg hz (div_nonneg (le_of_lt hu) (by norm_num only)))]
    dsimp only [G]
    rw [show (1 / 2 : ℝ) * u = u / 2 by ring, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ←
      mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 3
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi he, MeasureTheory.integral_const_mul]
  have h := MeasureTheory.integral_comp_mul_left_Ioi G 0 (by norm_num only : (0 : ℝ) < 1 / 2)
  rw [mul_zero, show (1 / 2 : ℝ)⁻¹ = 2 by norm_num only, Complex.real_smul] at h
  rw [h, Complex.ofReal_mul]
  dsimp only [G]
  ring

/-- For a pole at `-q` to the left of the forward contour, the coefficient
of the resolvent in H33 is the weighted finite convolution at rate `pole - q`. -/
theorem high_gamma_forward_pole (K : HighGaussianKernel) {q z : ℝ} (hq : -(9 / 16 : ℝ) < q)
    (hz : 0 ≤ z) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (r t) * Complex.exp (r t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (r t + (q : ℂ))⁻¹ * W t) =
        (Real.exp (-(K.pole : ℝ) * z) : ℂ) *
          ∫ v in (0 : ℝ)..z,
            ((Real.exp (((K.pole : ℝ) - q) * (z - v)) * K.realProfile.eval v : ℝ) : ℂ) := by
  intro r W hc hi
  let b := (9 / 16 + q) / 2
  have hb : 0 < b := by
    dsimp only [b]; linarith only [hq]
  have hm :=
    high_gamma_forward_moment K hb (by norm_num only : -(9 / 16 : ℝ) ≤ 9 / 16) le_rfl
      (by norm_num only) hz hc hi
  have he (t : ℝ) : (r t + (q : ℂ))⁻¹ = (2 : ℂ)⁻¹ * (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) := by
    rw [one_div, ← mul_inv]
    congr 1
    dsimp only [r, b]
    push_cast
    ring
  have hrate : (K.pole : ℝ) + 9 / 16 - 2 * b = (K.pole : ℝ) - q := by
    dsimp only [b]
    ring
  simp only [he, mul_assoc, MeasureTheory.integral_const_mul]
  rw [mul_left_comm, hm, hrate, Complex.ofReal_mul, Complex.ofReal_ofNat, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ (by norm_num only : (2 : ℂ) ≠ 0), one_mul]

/-- For a pole at `q` to the right of the reflected contour, the coefficient
of the resolvent in H33 is the weighted signed Laplace tail at rate `pole + q`. -/
theorem high_gamma_reflect_pole (K : HighGaussianKernel) {q z : ℝ} (hq : -(9 / 16 : ℝ) < q)
    (hz : 0 ≤ z) :
    let r := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (r t) * Complex.exp (r t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, ((q : ℂ) - r t)⁻¹ * W t) =
        (Real.exp (-(K.pole : ℝ) * z) : ℂ) *
          ∫ v in Set.Ioi (0 : ℝ),
            ((Real.exp (-((K.pole : ℝ) + q) * v) * K.realProfile.eval (z + v) : ℝ) : ℂ) := by
  intro r W hc hi
  let b := (q + 9 / 16) / 2
  have hb : 0 < b := by
    dsimp only [b]; linarith only [hq]
  have hm :=
    high_gamma_reflect_moment K (c := -9 / 16) hb (by norm_num only) (by norm_num only)
      (by norm_num only) hz hc hi
  have he (t : ℝ) : ((q : ℂ) - r t)⁻¹ = (2 : ℂ)⁻¹ * (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) := by
    rw [one_div, ← mul_inv]
    congr 1
    dsimp only [r, b]
    push_cast
    ring
  have hrate : (K.pole : ℝ) + (-9 / 16) + 2 * b = (K.pole : ℝ) + q := by
    dsimp only [b]
    ring
  simp only [he, mul_assoc, MeasureTheory.integral_const_mul]
  rw [mul_left_comm, hm, hrate, Complex.ofReal_mul, Complex.ofReal_ofNat, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ (by norm_num only : (2 : ℂ) ≠ 0), one_mul]

/-- The modulated square is continuous and integrable on the two contour
lines. The pole is strictly to the left of the entire contour band. -/
theorem high_gamma_weight_regular (K : HighGaussianKernel) {c X : ℝ} (hc : -(9 / 16 : ℝ) ≤ c)
    (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hX : 0 < X) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * (X : ℂ) ^ l t
    Continuous W ∧ MeasureTheory.Integrable W := by
  intro l W
  have hl : Continuous l := continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hd (t : ℝ) : l t + (K.pole : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [l, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, ← Complex.ofReal_ratCast,
      Complex.zero_re] at hr
    have hp : (9 / 16 : ℝ) < K.pole := by
      cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hr, hp, hc]
  have hd' (t : ℝ) : (l t + (K.pole : ℂ)) ^ (2 * K.degree + 4) ≠ 0 := pow_ne_zero _ (hd t)
  have hpoly :=
    (K.polynomial.map (Rat.castHom ℂ)).continuous.comp
      (hl.add (continuous_const (y := (K.pole : ℂ))))
  have hcp := hl.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  have hw : Continuous W := by
    dsimp only [W, highGaussianSquare]
    simp only [← Polynomial.eval_map]
    exact
      ((continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul hl))).mul
              (hpoly.pow _)).div
          ((hl.add continuous_const).pow _) hd' |>.mul
        hcp
  obtain ⟨A, hA⟩ := high_gamma_weight_quadratic K hc hc' hne hX
  refine ⟨hw, (integrable_inv_one_add_sq.const_mul A).mono' hw.aestronglyMeasurable ?_⟩
  exact MeasureTheory.ae_of_all _ fun t ↦ by simpa only [div_eq_mul_inv] using hA t

/-- The high Gaussian weights satisfy the hypotheses for termwise
integration of both vertical digamma difference series. -/
theorem high_gamma_digamma_exchange (K : HighGaussianKernel) {b c X : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hX : 0 < X) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * (X : ℂ) ^ l t
    ((∫ t : ℝ, (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
        ∑' n : ℕ,
          ∫ t : ℝ, (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t) ∧
      ((∫ t : ℝ,
          (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) - Complex.I * (t / 2))) * W t) := by
  intro l W
  obtain ⟨A, hA⟩ := high_gamma_weight_quadratic K hc hc' hne hX
  have hW : Continuous W := (high_gamma_weight_regular K hc hc' hne hX).1
  exact
    ⟨LLS.PaperStatements.quadratic_digamma_integral_eq_tsum hb W hW hA,
      LLS.PaperStatements.quadratic_reflected_digamma_eq_tsum hb W hW hA⟩

/-- At an exponential scale, the power form of the contour weight agrees
with the form used in the forward and reflected moment formulas. -/
theorem high_gamma_weight_exp (K : HighGaussianKernel) (w : ℂ) (z : ℝ) :
    highGaussianSquare K w * ((Real.exp (z - 5) : ℝ) : ℂ) ^ w =
      highGaussianSquare K w * Complex.exp (w * ((z - 5 : ℝ) : ℂ)) := by
  have h := Real.exp_pos (z - 5)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'), ← Complex.ofReal_log h.le,
    Real.log_exp, mul_comm ((z - 5 : ℝ) : ℂ)]

/-- The normalized integral of the weight alone is the physical profile
with its exponential factor. -/
theorem high_gamma_weight_integral (K : HighGaussianKernel) {c z : ℝ} (hc : -(9 / 16 : ℝ) ≤ c)
    (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) =
      ((Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z : ℝ) : ℂ) := by
  intro l W
  have he := high_gaussian_inverse_log K hc hc' hne z
  rw [ite_eq_left hz] at he
  rw [← he, Analysis.inverseMellin]
  apply congrArg (((1 / (2 * Real.pi) : ℝ) : ℂ) * ·)
  apply MeasureTheory.integral_congr_ae
  refine MeasureTheory.ae_of_all _ fun t ↦ ?_
  dsimp only
  have h := Real.exp_pos (5 - z)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'), ← Complex.ofReal_log h.le,
    Real.log_exp]
  dsimp only [W]
  congr 2
  push_cast
  ring

/-- Each term of the forward digamma series is a constant multiple of
the physical profile less a finite convolution at the corresponding rate. -/
theorem high_gamma_forward_diff (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / (b : ℂ) - 1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) =
      (1 / (b : ℂ)) * ((Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z : ℝ) : ℂ) -
        ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
          ∫ v in (0 : ℝ)..z,
            ((Real.exp (((K.pole : ℝ) + c - 2 * b) * (z - v)) * K.realProfile.eval v : ℝ) : ℂ) := by
  intro l W
  have hE : 0 < Real.exp (z - 5) := Real.exp_pos _
  obtain ⟨hW, hiW⟩ := high_gamma_weight_regular K hc hc' hne hE
  simp only [high_gamma_weight_exp] at hW hiW
  obtain ⟨A, hA⟩ := high_gamma_weight_quadratic K hc hc' hne hE
  simp only [high_gamma_weight_exp] at hA
  let f := fun t : ℝ ↦ (1 / (b : ℂ)) * W t
  let g := fun t : ℝ ↦ (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t
  have hf : MeasureTheory.Integrable f := hiW.const_mul _
  have hd : MeasureTheory.Integrable (fun t ↦ f t - g t) := by
    simpa only [f, g, sub_mul, mul_div_assoc] using
      (LLS.PaperStatements.quadratic_resolvent_integral_bound hb W hW hA).1
  have hg : MeasureTheory.Integrable g := by simpa only [Pi.sub_def, sub_sub_cancel] using hf.sub hd
  have he (t : ℝ) : (1 / (b : ℂ) - 1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t = f t - g t :=
    sub_mul _ _ _
  simp only [he]
  rw [MeasureTheory.integral_sub hf hg, mul_sub]
  dsimp only [f, g]
  rw [MeasureTheory.integral_const_mul, mul_left_comm, high_gamma_weight_integral K hc hc' hne hz,
    high_gamma_forward_moment K hb hc hc' hne hz hW hiW]

/-- Each term of the reflect digamma series is a constant multiple of
the physical profile less a signed Laplace tail at the corresponding rate. -/
theorem high_gamma_reflect_diff (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) =
      (1 / (b : ℂ)) * ((Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z : ℝ) : ℂ) -
        ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
          ∫ v in Set.Ioi (0 : ℝ),
            ((Real.exp (-((K.pole : ℝ) + c + 2 * b) * v) * K.realProfile.eval (z + v) : ℝ) :
              ℂ) := by
  intro l W
  have hE : 0 < Real.exp (z - 5) := Real.exp_pos _
  obtain ⟨hW, hiW⟩ := high_gamma_weight_regular K hc hc' hne hE
  simp only [high_gamma_weight_exp] at hW hiW
  obtain ⟨A, hA⟩ := high_gamma_weight_quadratic K hc hc' hne hE
  simp only [high_gamma_weight_exp] at hA
  let f := fun t : ℝ ↦ (1 / (b : ℂ)) * W t
  let g := fun t : ℝ ↦ (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t
  have hf : MeasureTheory.Integrable f := hiW.const_mul _
  have hd : MeasureTheory.Integrable (fun t ↦ f t - g t) := by
    have h :=
      (LLS.PaperStatements.quadratic_resolvent_integral_bound hb (fun t ↦ W (-t))
          (hW.comp continuous_neg) (fun t ↦ by simpa only [neg_sq] using hA (-t))).1.comp_neg
    simpa only [f, g, neg_neg, Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg, sub_mul,
      mul_div_assoc] using h
  have hg : MeasureTheory.Integrable g := by simpa only [Pi.sub_def, sub_sub_cancel] using hf.sub hd
  have he (t : ℝ) : (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t = f t - g t :=
    sub_mul _ _ _
  simp only [he]
  rw [MeasureTheory.integral_sub hf hg, mul_sub]
  dsimp only [f, g]
  rw [MeasureTheory.integral_const_mul, mul_left_comm, high_gamma_weight_integral K hc hc' hne hz,
    high_gamma_reflect_moment K hb hc hc' hne hz hW hiW]

/-- Integrate the forward digamma difference as a convergent series of
physical-profile constants minus finite convolution moments. -/
theorem high_gamma_forward_series (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ∑' n : ℕ,
        ((1 / ((b + n : ℝ) : ℂ)) * ((Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z : ℝ) : ℂ) -
          ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
            ∫ v in (0 : ℝ)..z,
              ((Real.exp (((K.pole : ℝ) + c - 2 * (b + n)) * (z - v)) * K.realProfile.eval v : ℝ) :
                ℂ)) := by
  intro l W
  have h := (high_gamma_digamma_exchange K hb hc hc' hne (Real.exp_pos (z - 5))).1
  simp only [high_gamma_weight_exp] at h
  rw [h, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [mul_div_assoc] using
    high_gamma_forward_diff K (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hc hc' hne hz

/-- Integrate the reflect digamma difference as a convergent series of
physical-profile constants minus signed Laplace tails. -/
theorem high_gamma_reflect_series (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ∑' n : ℕ,
        ((1 / ((b + n : ℝ) : ℂ)) * ((Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z : ℝ) : ℂ) -
          ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
            ∫ v in Set.Ioi (0 : ℝ),
              ((Real.exp (-((K.pole : ℝ) + c + 2 * (b + n)) * v) * K.realProfile.eval (z + v) : ℝ) :
                ℂ)) := by
  intro l W
  have h := (high_gamma_digamma_exchange K hb hc hc' hne (Real.exp_pos (z - 5))).2
  simp only [high_gamma_weight_exp] at h
  rw [h, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [mul_div_assoc] using
    high_gamma_reflect_diff K (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hc hc' hne hz

/-- The signed tail in the reflected contour formula is exactly the
finite derivative sum, with only the common exponential left outside. -/
theorem high_gamma_reflect_derivatives (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z)
    (hd : 0 < (K.pole : ℝ) + c + 2 * b) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    Continuous W →
      MeasureTheory.Integrable W →
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (1 / ((b : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) =
        ((2 * Real.exp (-(K.pole : ℝ) * z) : ℝ) : ℂ) *
          ((∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
                ((Polynomial.derivative^[j]) K.realProfile).eval z /
                  ((K.pole : ℝ) + c + 2 * b) ^ (j + 1) :
              ℝ) :
            ℂ) := by
  intro l W hW hiW
  rw [high_gamma_reflect_moment K hb hc hc' hne hz hW hiW, integral_complex_ofReal,
    gamma_shift_moment_derivatives K.realProfile z hd]

/-- For a forward pole farther left than the kernel pole, the contour term
equals an alternating derivative sum at the height less a decaying
endpoint contribution at zero. This applies to every H33 pole with index at least two. -/
theorem high_gamma_forward_pole_derivatives (K : HighGaussianKernel) {q z : ℝ}
    (hq : (K.pole : ℝ) < q) (hz : 0 ≤ z) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (r t) * Complex.exp (r t * ((z - 5 : ℝ) : ℂ))
    let d := q - (K.pole : ℝ)
    let A := fun y : ℝ ↦
      ∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
        (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) K.realProfile).eval y / d ^ (j + 1)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (r t + (q : ℂ))⁻¹ * W t) =
      (Real.exp (-(K.pole : ℝ) * z) : ℂ) * ((A z - Real.exp (-d * z) * A 0 : ℝ) : ℂ) := by
  intro r W d A
  have hq' : -(9 / 16 : ℝ) < q :=
    (by norm_num only : -(9 / 16 : ℝ) < 1 / 2).trans ((high_gaussian_pole_gt K).trans hq)
  obtain ⟨hW, hiW⟩ :=
    high_gamma_weight_regular K (c := 9 / 16) (by norm_num only) le_rfl (by norm_num only)
      (Real.exp_pos (z - 5))
  simp only [high_gamma_weight_exp] at hW hiW
  rw [high_gamma_forward_pole K hq' hz hW hiW]
  have he : (K.pole : ℝ) - q = -d := by
    dsimp only [d]
    ring
  rw [he, intervalIntegral.integral_ofReal,
    gamma_forward_decay_derivatives K.realProfile (sub_pos.mpr hq) hz]

/-- The origin derivative sum equals the rational continuation of the
complete transform at every real rate, including negative rates. -/
theorem high_gamma_origin_derivatives (K : HighGaussianKernel) (s : ℝ) :
    (∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
        ((Polynomial.derivative^[j]) K.realProfile).eval 0 / s ^ (j + 1)) =
      highProfileLaplace K s := by
  let N := 2 * K.degree + 3
  have hdeg : K.realProfile.natDegree ≤ N := by
    rw [← high_comp_profile_map,
      Polynomial.natDegree_map_eq_of_injective (Rat.cast_injective (α := ℝ))]
    exact high_rat_profile_degree K
  have hsum :=
    Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hdeg)) (f := fun j ↦
      ((Polynomial.derivative^[j]) K.realProfile).eval 0 / s ^ (j + 1))
      (fun j _ hj ↦ by
        have hj' : K.realProfile.natDegree < j :=
          Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
        rw [Polynomial.iterate_derivative_eq_zero hj', Polynomial.eval_zero, zero_div])
  rw [hsum, highProfileLaplace]
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul, HighGaussianKernel.realProfile,
    Polynomial.finsetSum_coeff, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hj : K.logPower j ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.add_le_add_right (Nat.sub_le _ _) 3))
  rw [Finset.sum_eq_single_of_mem (K.logPower j) hj]
  · rw [Polynomial.coeff_monomial, Finsupp.single_eq_same, ← mul_div_assoc, mul_div_cancel_left₀]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  · intro i _ hi
    rw [Polynomial.coeff_monomial, Finsupp.single_eq_of_ne hi, mul_zero, zero_div]

/-- The alternating origin term at decay rate `d` is minus the complete
square-kernel transform at the negative rate `-d`. -/
theorem high_gamma_origin_alternating (K : HighGaussianKernel) (d : ℝ) :
    (∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
        (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) K.realProfile).eval 0 / d ^ (j + 1)) =
      -highProfileLaplace K (-d) := by
  rw [← high_gamma_origin_derivatives, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (-d) ^ (j + 1) = -((-1 : ℝ) ^ j * d ^ (j + 1)) by
      rw [neg_eq_neg_one_mul d, mul_pow, pow_succ (-1 : ℝ), mul_neg_one, neg_mul]]
  rw [div_neg, neg_neg, div_mul_eq_div_div, div_eq_mul_inv _ ((-1 : ℝ) ^ j), ← inv_pow, inv_neg,
    inv_one, mul_comm ((-1 : ℝ) ^ j)]

/-- After subtracting the forward pole integral, the endpoint term is
a negative exponential multiple of the square transform. This is the
trivial-zero term in H33 for indices at least two. -/
theorem high_gamma_forward_pole_square (K : HighGaussianKernel) {q z : ℝ} (hq : (K.pole : ℝ) < q)
    (hz : 0 ≤ z) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (r t) * Complex.exp (r t * ((z - 5 : ℝ) : ℂ))
    let d := q - (K.pole : ℝ)
    let A := fun y : ℝ ↦
      ∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
        (-1 : ℝ) ^ j * ((Polynomial.derivative^[j]) K.realProfile).eval y / d ^ (j + 1)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, (r t + (q : ℂ))⁻¹ * W t) =
      (Real.exp (-(K.pole : ℝ) * z) : ℂ) *
        ((A z + Real.exp (-d * z) * highProfileLaplace K (-d) : ℝ) : ℂ) := by
  intro r W d A
  rw [high_gamma_forward_pole_derivatives K hq hz]
  have hA : A 0 = -highProfileLaplace K (-d) := high_gamma_origin_alternating K d
  change _ * ((A z - Real.exp (-d * z) * A 0 : ℝ) : ℂ) = _
  rw [hA, mul_neg, sub_neg_eq_add]

/-- The reflected digamma series has a finite derivative expansion after
the constant reciprocal difference and the higher powers are regrouped. -/
theorem high_gamma_reflect_coefficients (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 ≤ z)
    (hd : 0 < (K.pole : ℝ) + c + 2 * b) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    let d := (K.pole : ℝ) + c + 2 * b
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ((2 * Real.exp (-(K.pole : ℝ) * z) *
            (K.realProfile.eval z * (∑' n : ℕ, (1 / (2 * (b + n)) - 1 / (d + 2 * n))) +
              ∑ j ∈ Finset.range K.realProfile.natDegree,
                (-v (j + 1)) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) :
          ℝ) :
        ℂ) := by
  intro l W d v
  let F := fun n : ℕ ↦
    K.realProfile.eval z * (1 / (2 * (b + n)) - 1 / (d + 2 * n)) +
      ∑ j ∈ Finset.range K.realProfile.natDegree, (-v (j + 1)) / (d + 2 * n) ^ (j + 2)
  have hsum :=
    gamma_pole_coefficients_tsum hb hd K.realProfile.natDegree
      (fun j ↦ if j = 0 then K.realProfile.eval z else -v j)
  simp only [Nat.succ_ne_zero, ite_true, ite_false] at hsum
  change (∑' n, F n) = _ at hsum
  rw [high_gamma_reflect_series K hb hc hc' hne hz, ← hsum]
  conv_rhs => rw [Complex.ofReal_mul, Complex.ofReal_tsum F, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hdn : 0 < d + 2 * (n : ℝ) := by linarith only [hd, Nat.cast_nonneg (α := ℝ) n]
  have he : (K.pole : ℝ) + c + 2 * (b + n) = d + 2 * (n : ℝ) := by
    dsimp only [d]
    ring
  rw [he, integral_complex_ofReal, gamma_shift_moment_derivatives K.realProfile z hdn]
  dsimp only [F]
  rw [Finset.sum_range_succ', pow_one, Function.iterate_zero_apply]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, neg_div, Finset.sum_neg_distrib, Complex.ofReal_neg]
  dsimp only [v]
  rw [div_mul_eq_div_div (1 : ℂ) (2 : ℂ)]
  ring

/-- The forward digamma series has a finite derivative expansion after
the reciprocal differences are regrouped. The remaining exponential
series records the trivial-zero residues. -/
theorem high_gamma_forward_coefficients (K : HighGaussianKernel) {b c z : ℝ} (hb : 0 < b)
    (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 9 / 16) (hne : c ≠ -1 / 2) (hz : 0 < z)
    (hd : 1 ≤ 2 * b - c - (K.pole : ℝ)) :
    let l := fun t : ℝ ↦ (c : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    let d := 2 * b - c - (K.pole : ℝ)
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ((2 * Real.exp (-(K.pole : ℝ) * z) *
            (K.realProfile.eval z * (∑' n : ℕ, (1 / (2 * (b + n)) - 1 / (d + 2 * n))) +
                ∑ j ∈ Finset.range K.realProfile.natDegree,
                  (-((-1 : ℝ) ^ (j + 1) * v (j + 1))) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2)) -
              ∑' n : ℕ, Real.exp (-(d + 2 * n) * z) * highProfileLaplace K (-(d + 2 * n))) :
          ℝ) :
        ℂ) := by
  intro l W d v
  let F := fun n : ℕ ↦
    K.realProfile.eval z * (1 / (2 * (b + n)) - 1 / (d + 2 * n)) +
      ∑ j ∈ Finset.range K.realProfile.natDegree,
        (-((-1 : ℝ) ^ (j + 1) * v (j + 1))) / (d + 2 * n) ^ (j + 2)
  have hd₀ : 0 < d := zero_lt_one.trans_le hd
  have hsum :=
    gamma_pole_coefficients_tsum hb hd₀ K.realProfile.natDegree
      (fun j ↦ if j = 0 then K.realProfile.eval z else -((-1 : ℝ) ^ j * v j))
  simp only [Nat.succ_ne_zero, ite_true, ite_false] at hsum
  change (∑' n, F n) = _ at hsum
  let T := fun n : ℕ ↦ Real.exp (-(d + 2 * n) * z) * highProfileLaplace K (-(d + 2 * n))
  have hT : Summable T := by
    have h := high_gamma_trivial_tail_summable K (d := 4 - d) (by linarith only [hd]) hz
    apply (h.mul_left (Real.exp ((9 / 2 - d) * z))).congr
    intro n
    dsimp only [T]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  have hF : Summable F := by
    apply ((gamma_pole_diff_summable hb hd₀).mul_left (K.realProfile.eval z)).add
    apply summable_sum
    intro j _
    simpa only [mul_one_div] using
      (gamma_pole_power_summable hd₀ (Nat.zero_lt_succ j)).mul_left
        (-((-1 : ℝ) ^ (j + 1) * v (j + 1)))
  rw [high_gamma_forward_series K hb hc hc' hne hz.le, ← hsum]
  change _ = ((2 * Real.exp (-(K.pole : ℝ) * z) * ((∑' n, F n) - ∑' n, T n) : ℝ) : ℂ)
  rw [← hF.tsum_sub hT]
  conv_rhs => rw [Complex.ofReal_mul, Complex.ofReal_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hdn : 0 < d + 2 * (n : ℝ) := by linarith only [hd₀, Nat.cast_nonneg (α := ℝ) n]
  have he : (K.pole : ℝ) + c - 2 * (b + n) = -(d + 2 * (n : ℝ)) := by
    dsimp only [d]
    ring
  rw [he, intervalIntegral.integral_ofReal, gamma_forward_decay_derivatives K.realProfile hdn hz.le,
    high_gamma_origin_alternating]
  dsimp only [F, T]
  rw [Finset.sum_range_succ', pow_one, Function.iterate_zero_apply, pow_zero, one_mul, mul_neg,
    sub_neg_eq_add]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, neg_div, Finset.sum_neg_distrib, Complex.ofReal_neg]
  dsimp only [v]
  rw [div_mul_eq_div_div (1 : ℂ) (2 : ℂ)]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
