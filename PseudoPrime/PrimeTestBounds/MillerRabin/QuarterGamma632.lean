/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGamma107
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaConvolutionIntegral
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour600
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Gamma and contour bounds at radii 313 through 316 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Moving the center of an exponential Gamma convolution costs at most
the exponential of the displacement times the negative decay rate. -/
private theorem gamma_convolution_shift {x y c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-c * |x - y|) * quarterGammaConvolution x c ≤ quarterGammaConvolution y c := by
  unfold quarterGammaConvolution
  rw [← MeasureTheory.integral_const_mul]
  apply
    MeasureTheory.integral_mono_ae ((quarter_gamma_convolution_integrable x hc).const_mul _)
      (quarter_gamma_convolution_integrable y hc)
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro v hv
  have hp : 0 ≤ quarterGammaDensity v := by
    unfold quarterGammaDensity
    have hv0 : 0 ≤ v := hv.le
    rw [ite_eq_left hv0]
    positivity
  have ht : |v - y| ≤ |v - x| + |x - y| := by
    simpa only [sub_add_sub_cancel] using abs_add_le (v - x) (x - y)
  have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr hc))
  have hh := mul_le_mul_of_nonneg_left h hp
  rw [mul_add, Real.exp_add] at hh
  linarith only [hh,
    show
      quarterGammaDensity v * (Real.exp (-c * |v - x|) * Real.exp (-c * |x - y|)) =
        Real.exp (-c * |x - y|) * (quarterGammaDensity v * Real.exp (-c * |v - x|))
      by ring]

/-- Above radius 313, the anchor recovery loses at most 0.035 times the relative
increase in radius. The exponential convolution shift controls the loss. -/
theorem first_gamma_lower_from_313 {r : ℝ} (hr : 313 ≤ r) :
    0.035 * (1 - (r - 313) / 313) ≤
      ∫ v in Set.Ioi (0 : ℝ),
        gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log (r ^ 2) + 14 / 5)|) := by
  let z (a : ℝ) := Real.log (a ^ 2) + 14 / 5
  let x (a : ℝ) := 17 / 18 * z a
  have hr0 : 0 < r := by linarith only [hr]
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 313) hr
  have he := Real.log_le_sub_one_of_pos (div_pos hr0 (by norm_num only : (0 : ℝ) < 313))
  rw [Real.log_div hr0.ne' (by norm_num only)] at he
  have hx : 0 ≤ x r - x 313 := by
    dsimp only [x, z]
    rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have harg : -((r - 313) / 313) ≤ -(9 / 17) * |x 313 - x r| := by
    rw [abs_sub_comm, abs_of_nonneg hx]
    dsimp only [x, z]
    rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [he]
  have hfac : (1 - (r - 313) / 313) ≤ Real.exp (-(9 / 17) * |x 313 - x r|) := by
    linarith only [(Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr harg)]
  have h313 := section107_first_gamma (r := 313) (by norm_num only) le_rfl
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only] at h313 ⊢
  change 0.035 ≤ 18 / 17 * quarterGammaConvolution (x 313) (9 / 17) at h313
  change 0.035 * (1 - (r - 313) / 313) ≤ 18 / 17 * quarterGammaConvolution (x r) (9 / 17)
  have hq := gamma_convolution_shift (x := x 313) (y := x r) (c := 9 / 17) (by norm_num only)
  have h := mul_le_mul hfac h313 (by norm_num only) (Real.exp_pos _).le
  have hj := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 18 / 17)
  linarith only [h, hj]

/-- The Gamma recovery at radius 313 transfers to radii through 316.
The logarithmic length bound makes the loss at most (3/313) of the
left-endpoint recovery. -/
theorem first_gamma_lower_632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    0.03466 ≤
      ∫ v in Set.Ioi (0 : ℝ),
        gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log (r ^ 2) + 14 / 5)|) := by
  exact
    (show 0.03466 ≤ 0.035 * (1 - (r - 313) / 313) by linarith only [hr.2]).trans
      (first_gamma_lower_from_313 hr.1)

/-- The contour estimate retains the radius-dependent first Gamma recovery. -/
theorem even_contour_upper_from_313 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hi : χ⁻¹ ≠ 1)
    (he : χ.Even) {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    contourNonEuler570 χ (r ^ 2) ≤
      Real.log q * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ -
        (0.035 * (1 - (r - 313) / 313)) -
        (4 / 3 : ℝ) * gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have hp : 0 < r := by linarith only [hr.1]
  have hx := sq_pos_of_pos hp
  have hx1 := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have hz : 13 ≤ Real.log (r ^ 2) + 14 / 5 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h,
      Real.log_le_log (by norm_num only : (0 : ℝ) < 300)
        (show (300 : ℝ) ≤ r by linarith only [hr.1])]
  have hc := first_gamma_lower_from_313 hr.1
  have hn := central_gamma_convolution_upper χ he hx hz
  rw [← central_gamma_pair_eq_570 χ he hx, ← right_gamma_eq_central_570 χ hx, ←
    reflected_arch_eq_central_570 _ hi hx1, Complex.add_re] at hn
  unfold contourNonEuler570
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith only [hn, hc]

/-- For an even nonprincipal inverse character on the radius interval from 313 to 316,
the contour contribution retains the local density and the first Gamma recovery. -/
theorem even_contour_upper_632 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hi : χ⁻¹ ≠ 1)
    (he : χ.Even) {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    contourNonEuler570 χ (r ^ 2) ≤
      Real.log q * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ - 0.03466 -
        (4 / 3 : ℝ) * gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
  have h := even_contour_upper_from_313 χ hi he hr
  linarith only [h, hr.2]

/-- The contour estimate retains the radius-dependent first Gamma recovery. -/
theorem triple_contour_upper_from_313 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ}
    (hr : r ∈ Set.Icc 313 316) (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) :
    contourNonEuler570 a (r ^ 2) + contourNonEuler570 b (r ^ 2) + contourNonEuler570 c (r ^ 2) ≤
      section99Conductor r - 3 * (0.035 * (1 - (r - 313) / 313)) -
        4 * quarterWeight570 (r ^ 2) 1 := by
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hpos : 0 ≤ gammaDensity570 (Real.log (r ^ 2) + 14 / 5) := by
    unfold gammaDensity570
    split_ifs with h
    · positivity
    · exact le_rfl
  have hm := mul_le_mul_of_nonneg_right hlog hpos
  have ha := even_contour_upper_from_313 a ia ea hr
  have hb := even_contour_upper_from_313 b ib eb hr
  have hc := even_contour_upper_from_313 c ic ec hr
  rw [section99_profile_eq_density hr₁] at ha hb hc
  rw [section99_conductor_eq_density hr₁, section99_weight_eq_density hr₁]
  linarith only [ha, hb, hc, hm]

/-- Sum the three even contour estimates using their common log-conductor
bound and keep the exact density term for later cancellation. -/
theorem triple_contour_upper_632 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) (ea : a.Even) (eb : b.Even) (ec : c.Even) {r : ℝ}
    (hr : r ∈ Set.Icc 313 316) (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) :
    contourNonEuler570 a (r ^ 2) + contourNonEuler570 b (r ^ 2) + contourNonEuler570 c (r ^ 2) ≤
      section99Conductor r - 3 * 0.03466 - 4 * quarterWeight570 (r ^ 2) 1 := by
  have h := triple_contour_upper_from_313 a b c ia ib ic ea eb ec hr hlog
  linarith only [h, hr.2]

end PseudoPrime.PrimeTestBounds.MillerRabin
