/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineXi656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineXi656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxNumerics656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxEuler656

/-! # Section 132 conductor and shifted half-point coefficient -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient of the radius from the seven shifted positive half-point poles. -/
noncomputable def quarterAuxHalfCoeff656 : ℝ :=
  (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6) *
    ∑ i, quarterAuxCoeff656 i * Real.exp (-(quarterAuxShift656 i : ℝ) / 2)

private noncomputable def expTaylor (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 54, x ^ j / (j.factorial : ℝ)

private theorem exp_taylor_cast (x : ℚ) : (auxExpTaylor656 x : ℝ) = expTaylor x := by
  simp only [auxExpTaylor656, expTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

private theorem exp_taylor_error (x : ℚ) (hx : |x| ≤ 10) :
    |Real.exp (x : ℝ) - expTaylor x| ≤ 1 / 10 ^ 16 := by
  rw [← exp_taylor_cast]
  exact aux_exp_error_656 x (by exact_mod_cast hx)

private def mixedRat (F : ℚ → ℚ) : ℚ :=
  (∑ i,
        ∑ j,
          quarterAuxCoeffRat656 i * quarterAuxCoeffRat656 j * F (auxFrequency i - auxFrequency j)) /
      2 -
    ∑ i, quarterAuxCoeffRat656 i * F (auxFrequency i)

private theorem mixed_rat_cast (F : ℚ → ℚ) (G : ℝ → ℝ) (h : ∀ t : ℚ, (F t : ℝ) = G t) :
    (mixedRat F : ℝ) = quarterAuxMix656 G := by
  simp only [mixedRat, quarterAuxMix656, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_mul,
    Rat.cast_ofNat, aux_frequency_cast, aux_coeff_cast, h]

private noncomputable def conductorProfile (t : ℝ) : ℝ :=
  2 * Real.exp (-(11 / 10) * |t|) * quarterAuxProfile656 |t|

private noncomputable def conductorApprox (t : ℝ) : ℝ :=
  2 * expTaylor (-(11 / 10) * |t|) * quarterAuxProfile656 |t|

private def conductorApproxRat (t : ℚ) : ℚ :=
  2 * auxExpTaylor656 (-(11 / 10) * |t|) * profileConstant |t|

private theorem conductor_approx_cast (t : ℚ) : (conductorApproxRat t : ℝ) = conductorApprox t := by
  simp only [conductorApproxRat, conductorApprox, exp_taylor_cast, profileConstant,
    quarterAuxProfile656, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_abs, Rat.cast_div,
    Rat.cast_neg, Rat.cast_ofNat]
  ring

private theorem conductor_approx_error (t : ℚ) (ht : |((11 / 10 : ℚ) * |t|)| ≤ 10)
    (hq : |profileConstant (|t|)| ≤ 50) :
    |conductorProfile t - conductorApprox t| ≤ 1 / 10 ^ 14 := by
  have hp := exp_taylor_error (-(11 / 10) * |t|) (by simpa only [neg_mul, abs_neg] using ht)
  have hq' : |quarterAuxProfile656 (|(t : ℝ)|)| ≤ 50 := by
    have hqR : |(profileConstant (|t|) : ℝ)| ≤ 50 := by exact_mod_cast hq
    simp only [profileConstant, quarterAuxProfile656, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
      Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] at hqR ⊢
    convert hqR using 2
    ring
  simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_abs, Rat.cast_ofNat] at hp
  have he :
    conductorProfile t - conductorApprox t =
      (2 * (Real.exp (-(11 / 10) * |(t : ℝ)|) - expTaylor (-(11 / 10) * |(t : ℝ)|))) *
        quarterAuxProfile656 |(t : ℝ)| := by
    unfold conductorProfile conductorApprox
    ring
  rw [he, abs_mul, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  exact
    (mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num only)) hq' (abs_nonneg _)
          (by norm_num only)).trans
      (by norm_num only)

private theorem conductor_profile_eq :
    quarterAuxMix656 conductorProfile = 4 * quarterAuxConductor656 := by
  have h (t : ℝ) : conductorProfile t = quarterSymmetricProfile656 (Real.exp |t|)⁻¹ * 4 := by
    rw [symmetric_profile_value (inv_pos.mpr (Real.exp_pos _)), Real.log_inv, Real.log_exp, abs_neg,
      abs_abs]
    unfold conductorProfile
    ring
  rw [funext h, aux_mix_scale_656, mul_comm]
  rfl

private def shiftedExpSumRat (v : Fin 7 → ℚ) : ℚ :=
  ∑ i, quarterAuxCoeffRat656 i * auxExpTaylor656 (v i)

private theorem shifted_exp_sum_error (v : Fin 7 → ℚ) (hs : ∀ i, |v i| ≤ 10) :
    |(∑ i, quarterAuxCoeff656 i * Real.exp (v i : ℝ)) - (shiftedExpSumRat v : ℝ)| ≤
      7 / 10 ^ 16 := by
  have hc : ∀ i : Fin 7, |quarterAuxCoeffRat656 i| ≤ 1 := by decide +kernel
  unfold shiftedExpSumRat
  simp only [Rat.cast_sum, Rat.cast_mul, exp_taylor_cast, aux_coeff_cast, ← Finset.sum_sub_distrib,
    ← mul_sub]
  refine (Finset.abs_sum_le_sum_abs (s := Finset.univ) _).trans ?_
  have hr (i : Fin 7) :
    |quarterAuxCoeff656 i * (Real.exp (v i : ℝ) - expTaylor (v i : ℝ))| ≤ 1 / 10 ^ 16 := by
    have h : |quarterAuxCoeff656 i| ≤ 1 := by
      rw [← aux_coeff_cast]
      exact_mod_cast hc i
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) h).trans (exp_taylor_error _ (hs i))
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hr i)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  linarith only [h]

private def halfSumRat : ℚ :=
  shiftedExpSumRat (fun i ↦ -quarterAuxShift656 i / 2)

private theorem half_sum_error :
    |(∑ i, quarterAuxCoeff656 i * Real.exp (-(quarterAuxShift656 i : ℝ) / 2)) - (halfSumRat : ℝ)| ≤
      7 / 10 ^ 16 := by
  simpa only [halfSumRat, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using
    shifted_exp_sum_error (fun i ↦ -quarterAuxShift656 i / 2) (by decide +kernel)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation checks the signed Taylor sums at all relevant frequencies.
/-- The symmetric conductor and positive half-point coefficients give
the strict linear gain from equation (132.14). -/
theorem quarter_aux_delta_lower_656 :
    (0.00022760 : ℝ) < -4 * quarterAuxConductor656 - quarterAuxHalfCoeff656 := by
  have hq₁ : ∀ i, |profileConstant (|auxFrequency i|)| ≤ 50 := by decide +kernel
  have hq₂ : ∀ i j, |profileConstant (|auxFrequency i - auxFrequency j|)| ≤ 50 := by decide +kernel
  have h :=
    quarter_aux_mix_bound_656 (fun t ↦ conductorProfile t - conductorApprox t)
      (by norm_num only : (0 : ℝ) ≤ 1 / 10 ^ 14)
      (fun i ↦ by
        simpa only [aux_frequency_cast] using
          conductor_approx_error (auxFrequency i) (aux_exp_arguments_656.1 i) (hq₁ i))
      (fun i j ↦ by
        have he : |((11 / 10 : ℚ) * |auxFrequency i - auxFrequency j|)| ≤ 10 := by
          simpa only [auxFrequency, add_sub_add_left_eq_sub] using aux_exp_arguments_656.2 i j
        simpa only [Rat.cast_sub, aux_frequency_cast] using conductor_approx_error _ he (hq₂ i j))
  have he :
    quarterAuxMix656 (fun t ↦ conductorProfile t - conductorApprox t) =
      quarterAuxMix656 conductorProfile - quarterAuxMix656 conductorApprox := by
    unfold quarterAuxMix656
    simp only [mul_sub, Finset.sum_sub_distrib, sub_div]
    ring
  rw [he, conductor_profile_eq, ← mixed_rat_cast _ _ conductor_approx_cast] at h
  have hj₀ : mixedRat conductorApproxRat ≤ 62799021 / 10 ^ 10 := by decide +kernel
  have hj₀R := (Rat.cast_le (K := ℝ)).mpr hj₀
  have hj₁ : (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6 : ℚ) * halfSumRat ≤ -65075076 / 10 ^ 10 := by
    decide +kernel
  have hj₁R := (Rat.cast_le (K := ℝ)).mpr hj₁
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg] at hj₀R hj₁R
  have hd := (abs_le.mp h).2
  have hh := (abs_le.mp half_sum_error).2
  unfold quarterAuxHalfCoeff656
  linarith only [hd, hh, hj₀R, hj₁R]

/-- At a positive radius, the shifted positive half-point residue is
linear in the radius, with the exponential of minus half the displacement. -/
theorem quarter_shifted_half_pole_656 {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let x := r ^ 2 * Real.exp (-(21 / 8 + h))
    (quarterKernel656.function (1 / 2) * (x : ℂ) ^ (1 / 2 : ℂ)).re =
      ((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6) * r * Real.exp (-h / 2) := by
  intro x
  have he : Real.log x * (1 / 2) = Real.log r - (21 / 8 + h) / 2 := by
    dsimp only [x]
    rw [Real.log_mul (pow_ne_zero _ hr.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    ring
  have hx : 0 < x := mul_pos (pow_pos hr _) (Real.exp_pos _)
  have hf :
    quarterKernel656.function (1 / 2) =
      ((((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6) * Real.exp (21 / 16) : ℝ) : ℂ) := by
    rw [quarter_function_656, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    norm_num only
    ring
  rw [hf,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by
      norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat],
    ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul, Complex.ofReal_re, Real.rpow_def_of_pos hx,
    he, Real.exp_sub, Real.exp_log hr]
  rw [show ((21 / 8 : ℝ) + h) / 2 = 21 / 16 + h / 2 by ring, Real.exp_add, neg_div, Real.exp_neg]
  calc
    _ =
        ((11 / 10 : ℝ) ^ 5 / (8 / 5) ^ 6 * r * (Real.exp (h / 2))⁻¹) *
          (Real.exp (21 / 16) * (Real.exp (21 / 16))⁻¹) :=
      by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]

/-- The shifted forward comparison with the positive half-point residues
added back into each summand. The residues are accounted for by the linear gain. -/
noncomputable def quarterShiftCorrected656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (r : ℝ) :
    ℝ :=
  quarterShiftedForward656 χ (r ^ 2) +
    ∑ i,
      quarterAuxCoeff656 i *
        (quarterKernel656.function (1 / 2) *
            ((r ^ 2 * Real.exp (-(quarterAuxFrequency656 i)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)).re

private theorem shift_corrected_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {r : ℝ}
    (hr : 0 < r) :
    quarterShiftCorrected656 χ r =
      quarterShiftedForward656 χ (r ^ 2) + quarterAuxHalfCoeff656 * r / 3 := by
  have h (i : Fin 7) := quarter_shifted_half_pole_656 hr (quarterAuxShift656 i : ℝ)
  unfold quarterShiftCorrected656 quarterAuxHalfCoeff656
  simp only [quarterAuxFrequency656, h]
  simp only [mul_assoc, mul_left_comm (quarterAuxCoeff656 _), ← Finset.mul_sum]
  ring

/-- At total log conductor four times the radius, the forward comparison
absorbs the positive shifted residues and retains the certified linear gain. -/
theorem quarter_forward_linear_gain_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hs : 2 ≤ s)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {r : ℝ} (hr : 322 ≤ r)
    (hL : Real.log p + Real.log q + Real.log s = 4 * r)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hpb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hpc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    (∑' n, quarterKernel656.summand a (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand b (r ^ 2) n).re +
        (∑' n, quarterKernel656.summand c (r ^ 2) n).re +
        (quarterShiftCorrected656 a r + quarterShiftCorrected656 b r +
          quarterShiftCorrected656 c r) +
        3.673430088 +
        0.00022760 * r ≤
      quarterCosineContour656 a 0 + quarterCosineContour656 b 0 + quarterCosineContour656 c 0 +
        ((contourRemainder656 a (r ^ 2)).re + (contourRemainder656 b (r ^ 2)).re +
          (contourRemainder656 c (r ^ 2)).re) := by
  have hX := pow_le_pow_left₀ (by norm_num only : 0 ≤ (322 : ℝ)) hr 2
  have h := quarter_forward_residue_gain_656 ha hb hc hp hq hs hG hX ht hpa hpb hpc
  have hr₀ : 0 < r := by linarith only [hr]
  have hd := mul_le_mul_of_nonneg_right quarter_aux_delta_lower_656.le hr₀.le
  rw [hL] at h
  rw [shift_corrected_eq a hr₀, shift_corrected_eq b hr₀, shift_corrected_eq c hr₀]
  linarith only [h, hd]

/-- The negative half-point residue at a shifted scale is an inverse
radius times the exponential of half the displacement. -/
theorem quarter_shifted_neg_pole_656 {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let x := r ^ 2 * Real.exp (-(21 / 8 + h))
    (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re =
      ((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6) / r * Real.exp (h / 2) := by
  intro x
  have hl : Real.log x * (-1 / 2) = (21 / 8 + h) / 2 - Real.log r := by
    dsimp only [x]
    rw [Real.log_mul (pow_ne_zero _ hr.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    ring
  have hx : 0 < x := mul_pos (pow_pos hr _) (Real.exp_pos _)
  have hf :
    quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) =
      ((((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6) * Real.exp (-(21 / 16))) : ℝ) := by
    rw [quarter_function_656, Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    norm_num only
    ring
  rw [hf, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul, Complex.ofReal_re,
    Real.rpow_def_of_pos hx, hl, Real.exp_sub, Real.exp_log hr,
    show ((21 / 8 : ℝ) + h) / 2 = 21 / 16 + h / 2 by ring, Real.exp_add, Real.exp_neg]
  calc
    _ =
        ((11 / 10 : ℝ) ^ 5 / (3 / 5) ^ 6 / r * Real.exp (h / 2)) *
          (Real.exp (21 / 16) * (Real.exp (21 / 16))⁻¹) :=
      by ring
    _ = _ := by rw [mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]

/-- The signed negative half-point coefficient in equation (132.16). -/
noncomputable def quarterAuxNegPole656 : ℝ :=
  -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6) *
    ∑ i, quarterAuxCoeff656 i * Real.exp ((quarterAuxShift656 i : ℝ) / 2)

/-- Both bounds on the negative half-point coefficient are certified by
the shared exponential Taylor sum. The upper bound is useful for monotonicity. -/
theorem quarter_aux_neg_pole_box_656 : quarterAuxNegPole656 ∈ Set.Icc 19.24138528 19.24138529 := by
  let v : Fin 7 → ℚ := fun i ↦ quarterAuxShift656 i / 2
  have hv : ∀ i, |v i| ≤ 10 := by decide +kernel
  have h := shifted_exp_sum_error v hv
  simp only [v, Rat.cast_div, Rat.cast_ofNat] at h
  have hj :
    -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6 : ℚ) * shiftedExpSumRat v ∈
      Set.Icc (192413852839 / 10 ^ 10) (192413852842 / 10 ^ 10) := by
    decide +kernel
  have hlo := (Rat.cast_le (K := ℝ)).mpr hj.1
  have hhi := (Rat.cast_le (K := ℝ)).mpr hj.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_mul, Rat.cast_pow] at hlo hhi
  unfold quarterAuxNegPole656
  exact ⟨by linarith only [(abs_le.mp h).2, hlo], by linarith only [(abs_le.mp h).1, hhi]⟩

/-- The negative half-point residues in the shifted contour difference
sum to the certified coefficient divided by the radius. -/
theorem quarter_aux_neg_pole_sum_656 {r : ℝ} (hr : 0 < r) :
    -3 *
        (∑ i,
          quarterAuxCoeff656 i *
            (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) *
                ((r ^ 2 * Real.exp (-(quarterAuxFrequency656 i)) : ℝ) : ℂ) ^
                  ((-1 / 2 : ℝ) : ℂ)).re) =
      quarterAuxNegPole656 / r := by
  have h (i : Fin 7) := quarter_shifted_neg_pole_656 hr (quarterAuxShift656 i : ℝ)
  unfold quarterAuxNegPole656
  simp only [quarterAuxFrequency656, h]
  simp only [mul_left_comm (quarterAuxCoeff656 _), ← Finset.mul_sum]
  ring

/-- The signed fifth-degree conductor polynomial of equation (132.15). -/
noncomputable def quarterAuxConductorPoly656 (v : ℝ) : ℝ :=
  -(∑ i,
      quarterAuxCoeff656 i * Real.exp ((11 / 10) * (quarterAuxShift656 i : ℝ)) *
        (v - quarterAuxShift656 i) ^ 5)

/-- The sum of the shifted conductors factors into a power of the radius
and the common logarithmic polynomial. -/
noncomputable def quarterAuxTheta656 (r : ℝ) : ℝ :=
  -(11 / 10) ^ 5 / 30 * r ^ (-(6 / 5) : ℝ) * quarterAuxConductorPoly656 (2 * Real.log r)

private theorem aux_conductor_factor {r : ℝ} (hr : 0 < r) (h : ℝ) :
    let z := (11 / 10 : ℝ) * (2 * Real.log r - h)
    4 * r * (z ^ 5 * Real.exp (-z) / 120) =
      ((11 / 10 : ℝ) ^ 5 / 30 * r ^ (-(6 / 5) : ℝ)) *
        (Real.exp ((11 / 10) * h) * (2 * Real.log r - h) ^ 5) := by
  intro z
  have hp : r ^ (-(6 / 5) : ℝ) = r * Real.exp (-(11 / 5) * Real.log r) := by
    rw [Real.rpow_def_of_pos hr,
      show Real.log r * (-(6 / 5) : ℝ) = Real.log r + -(11 / 5) * Real.log r by ring, Real.exp_add,
      Real.exp_log hr]
  have he : -z = -(11 / 5) * Real.log r + (11 / 10) * h := by
    dsimp only [z]; ring
  rw [he, Real.exp_add, hp]
  dsimp only [z]
  ring

private theorem aux_conductor_profile {r : ℝ} (hr : 322 ≤ r) (i : Fin 7) :
    let x := r ^ 2 * Real.exp (-(quarterAuxFrequency656 i))
    let z := (11 / 10 : ℝ) * (2 * Real.log r - (quarterAuxShift656 i : ℝ))
    (quarterKernel656.transform x⁻¹).re = z ^ 5 * Real.exp (-z) / 120 := by
  intro x z
  have hr₀ : 0 < r := by linarith only [hr]
  have hX := pow_le_pow_left₀ (by norm_num only : 0 ≤ (322 : ℝ)) hr 2
  have hx : 1 ≤ x := quarter_aux_scale_ge_one_656 hX i
  have hx₀ := zero_lt_one.trans_le hx
  have hl : Real.log x⁻¹ = 21 / 8 + quarterAuxShift656 i - 2 * Real.log r := by
    dsimp only [x, quarterAuxFrequency656]
    rw [Real.log_inv, Real.log_mul (pow_ne_zero _ hr₀.ne') (Real.exp_pos _).ne', Real.log_pow,
      Real.log_exp]
    ring
  have hs : Real.log x⁻¹ ≤ 21 / 8 :=
    (Real.log_nonpos (inv_pos.mpr hx₀).le (inv_le_one_of_one_le₀ hx)).trans (by norm_num only)
  rw [quarter_transform_656 (inv_pos.mpr hx₀) hs, hl]
  have hz : (11 / 10 : ℝ) * (21 / 8 - (21 / 8 + quarterAuxShift656 i - 2 * Real.log r)) = z := by
    dsimp only [z]
    ring
  rw [hz]

/-- At total log conductor four times the radius, summing the shifted
conductor terms gives exactly the function used in the auxiliary residual. -/
theorem quarter_aux_theta_sum_656 {r : ℝ} (hr : 322 ≤ r) :
    (∑ i,
        quarterAuxCoeff656 i *
          (4 * r *
            (quarterKernel656.transform (r ^ 2 * Real.exp (-(quarterAuxFrequency656 i)))⁻¹).re)) =
      quarterAuxTheta656 r := by
  have hr₀ : 0 < r := by linarith only [hr]
  have he (i : Fin 7) := aux_conductor_profile hr i
  have hf (i : Fin 7) := aux_conductor_factor hr₀ (quarterAuxShift656 i : ℝ)
  dsimp only at he hf
  unfold quarterAuxTheta656 quarterAuxConductorPoly656
  simp only [he, hf]
  simp only [mul_assoc, mul_left_comm (quarterAuxCoeff656 _), ← Finset.mul_sum]
  ring

/-- The shifted conductor and negative half-point parts of the three
remainders have the common value in equation (132.16). -/
theorem quarter_aux_shift_signed_656 {r : ℝ} (hr : 322 ≤ r) :
    let x := fun i ↦ r ^ 2 * Real.exp (-(quarterAuxFrequency656 i))
    (∑ i,
        quarterAuxCoeff656 i *
          (4 * r * (quarterKernel656.transform (x i)⁻¹).re -
            3 *
              (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x i : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re)) =
      quarterAuxTheta656 r + quarterAuxNegPole656 / r := by
  intro x
  have hp := quarter_aux_neg_pole_sum_656 (by linarith only [hr] : 0 < r)
  have hc := quarter_aux_theta_sum_656 hr
  let f := fun i ↦
    (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x i : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re
  have hn : (∑ i, quarterAuxCoeff656 i * (3 * f i)) = 3 * ∑ i, quarterAuxCoeff656 i * f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ mul_left_comm _ _ _)
  change
    (∑ i, quarterAuxCoeff656 i * (4 * r * (quarterKernel656.transform (x i)⁻¹).re - 3 * f i)) = _
  simp only [mul_sub, Finset.sum_sub_distrib, hn]
  dsimp only [f, x]
  linear_combination hc + hp

end PseudoPrime.PrimeTestBounds.MillerRabin
