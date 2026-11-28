/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Reflection
import PseudoPrime.Analysis.PositiveTaylorTransport
import PseudoPrime.Analysis.ExponentialMomentTail
import PseudoPrime.Analysis.ExponentialTaylorRatio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! # Rational logarithm and root bounds at the K131 bridge endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem log_twice_bounds (y a b : ℚ) (j : ℕ) (hy : 0 < y) (hd : |1 - y / 2 ^ j| < 1)
    (ha : a ≤ 2 * Analysis.rationalLogLower y j 20)
    (hb : 2 * Analysis.rationalLogUpper y j 20 ≤ b) :
    2 * Real.log (y : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
  have h := Analysis.rationalLogBounds_sound hy j 20 hd
  have hl : (a : ℝ) ≤ 2 * (Analysis.rationalLogLower y j 20 : ℝ) := by exact_mod_cast ha
  have hu : 2 * (Analysis.rationalLogUpper y j 20 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  exact ⟨by linarith only [h.1, hl], by linarith only [h.2, hu]⟩

/-- The twice-logarithm of the left K131 radius lies between two
consecutive (10^{-7})-spaced rationals, by a dyadic Taylor bound. -/
theorem k131_left_log_bounds :
    2 * Real.log (465644807 / 400000) ∈
      Set.Icc (141194277 / 10000000 : ℝ) (141194278 / 10000000) := by
  have h :=
    log_twice_bounds (465644807 / 400000) (141194277 / 10000000) (141194278 / 10000000) 10
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The twice-logarithm of the right K131 radius lies between two
consecutive (10^{-7})-spaced rationals, by a dyadic Taylor bound. -/
theorem k131_right_log_bounds :
    2 * Real.log (1036273 / 250) ∈ Set.Icc (166593605 / 10000000 : ℝ) (166593606 / 10000000) := by
  have h :=
    log_twice_bounds (1036273 / 250) (166593605 / 10000000) (166593606 / 10000000) 12
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

private theorem eighth_root_bounds {y a b : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : a ^ (8 : ℕ) ≤ y) (hu : y ≤ b ^ (8 : ℕ)) : y ^ (1 / 8 : ℝ) ∈ Set.Icc a b := by
  have hp : (y ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num only [Nat.cast_ofNat, div_mul_cancel₀, OfNat.ofNat_ne_zero, Real.rpow_one]
  have hz := Real.rpow_nonneg hy (1 / 8 : ℝ)
  refine
    ⟨(pow_le_pow_iff_left₀ ha hz (by decide : (8 : ℕ) ≠ 0)).mp ?_,
      (pow_le_pow_iff_left₀ hz hb (by decide : (8 : ℕ) ≠ 0)).mp ?_⟩
  · rw [hp]
    exact hl
  · rw [hp]
    exact hu

/-- Reduce every eighth-integer exponent in the K131 endpoint comparison
to an integer power of the single eighth root of the radius. -/
theorem k131_rpow_eighth {y : ℝ} (hy : 0 ≤ y) (q : ℤ) :
    y ^ ((q : ℝ) / 8) = (y ^ (1 / 8 : ℝ)) ^ q := by
  have he : (q : ℝ) / 8 = (1 / 8 : ℝ) * q := by ring
  rw [he, Real.rpow_mul hy, Real.rpow_intCast]

/-- Bound the eighth root of the left K131 radius by testing the eighth
powers of the rational endpoints. -/
theorem k131_left_root_bounds :
    (465644807 / 400000 : ℝ) ^ (1 / 8 : ℝ) ∈
      Set.Icc (24168480494 / 10000000000 : ℝ) (24168480495 / 10000000000) := by
  apply eighth_root_bounds <;> norm_num only

/-- Bound the eighth root of the right K131 radius by testing the eighth
powers of the rational endpoints. -/
theorem k131_right_root_bounds :
    (1036273 / 250 : ℝ) ^ (1 / 8 : ℝ) ∈
      Set.Icc (28326425319 / 10000000000 : ℝ) (28326425320 / 10000000000) := by
  apply eighth_root_bounds <;> norm_num only

private theorem log_interval_image {x : ℝ} {a b c d : ℚ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ))
    (ha : 0 < a) (hb : 0 < b) (hda : |1 - a / 2 ^ 4| < 1) (hdb : |1 - b / 2 ^ 4| < 1)
    (hc : c ≤ Analysis.rationalLogLower a 4 20) (hd : Analysis.rationalLogUpper b 4 20 ≤ d) :
    Real.log x ∈ Set.Icc (c : ℝ) (d : ℝ) := by
  have ha' : (0 : ℝ) < (a : ℝ) := (Rat.cast_pos (K := ℝ)).mpr ha
  have hl := Real.log_le_log ha' hx.1
  have hu := Real.log_le_log (ha'.trans_le hx.1) hx.2
  exact
    ⟨((Rat.cast_le (K := ℝ)).mpr hc).trans
        ((Analysis.rationalLogBounds_sound ha 4 20 hda).1.trans hl),
      hu.trans
        ((Analysis.rationalLogBounds_sound hb 4 20 hdb).2.trans ((Rat.cast_le (K := ℝ)).mpr hd))⟩

/-- Bound the iterated logarithm used by the principal error at the
left K131 radius, applying monotonicity to the twice-logarithm enclosure. -/
theorem k131_left_log_log_bounds :
    Real.log (2 * Real.log (465644807 / 400000)) ∈
      Set.Icc (26475516 / 10000000 : ℝ) (26475518 / 10000000) := by
  have h :=
    log_interval_image (a := 141194277 / 10000000) (b := 141194278 / 10000000) (c :=
      26475516 / 10000000) (d := 26475518 / 10000000)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using k131_left_log_bounds) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- Bound the iterated logarithm used by the principal error at the
right K131 radius, applying monotonicity to the twice-logarithm enclosure. -/
theorem k131_right_log_log_bounds :
    Real.log (2 * Real.log (1036273 / 250)) ∈
      Set.Icc (28129722 / 10000000 : ℝ) (28129723 / 10000000) := by
  have h :=
    log_interval_image (a := 166593605 / 10000000) (b := 166593606 / 10000000) (c :=
      28129722 / 10000000) (d := 28129723 / 10000000)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using k131_right_log_bounds) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- Integer exponents for the eight polynomial terms of the K131 gap,
with the eighth root of the radius as their common base. -/
def k131GapPower : Fin 8 → ℤ :=
  ![8, 0, -8, -19, -27, -40, -46, -54]

private theorem k131_gap_power_eq (j : Fin 8) :
    -gaussianK131GapExponent j = (k131GapPower j : ℝ) / 8 := by
  fin_cases j
  · change -(-1 : ℝ) = ((8 : ℤ) : ℝ) / 8
    norm_num only
  · change -(0 : ℝ) = ((0 : ℤ) : ℝ) / 8
    norm_num only
  · change -(1 : ℝ) = ((-8 : ℤ) : ℝ) / 8
    norm_num only
  · change -(19 / 8 : ℝ) = ((-19 : ℤ) : ℝ) / 8
    norm_num only
  · change -(27 / 8 : ℝ) = ((-27 : ℤ) : ℝ) / 8
    norm_num only
  · change -(5 : ℝ) = ((-40 : ℤ) : ℝ) / 8
    norm_num only
  · change -(23 / 4 : ℝ) = ((-46 : ℤ) : ℝ) / 8
    norm_num only
  · change -(27 / 4 : ℝ) = ((-54 : ℤ) : ℝ) / 8
    norm_num only

/-- Express the gap using only the eighth root, twice the logarithm, its
logarithm, and the coefficients of the gap polynomials. -/
theorem k131_gap_eval_root {y : ℝ} (hy : 0 ≤ y) :
    gaussianK131Gap y =
      let l := 2 * Real.log y
      let r := y ^ (1 / 8 : ℝ)
      (∑ j : Fin 8, r ^ (k131GapPower j) * (gaussianK131GapPoly j).eval l) +
        ((-gaussianK131RhCoeff) * (l * (l - Real.log l)) +
          r ^ (-4 : ℤ) * (-((81 / 100 : ℝ) * gaussianK131RecoveryVariation))) := by
  have h : -(1 / 2 : ℝ) = ((-4 : ℤ) : ℝ) / 8 := by norm_num only
  simp only [gaussianK131Gap, logPowerPoly, k131_gap_power_eq, k131_rpow_eighth hy,
    k131PrincipalError, Polynomial.eval_C, h]

private theorem exp_edge_upper : Real.exp (-(27 / 16 : ℝ) * (9 / 4)) ≤ 224408 / 10000000 := by
  have ht := Analysis.gamma_positive_taylor_le_exp (t := 243 / 64) (by norm_num only) 24
  have hr : (10000000 / 224408 : ℝ) ≤ Real.exp (243 / 64) := by
    have hq : (10000000 / 224408 : ℚ) ≤ Analysis.gammaPositiveTaylor (243 / 64) 24 := by
      decide +kernel
    have h := ((Rat.cast_le (K := ℝ)).mpr hq).trans ht
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  have h : -(27 / 16 : ℝ) * (9 / 4) = -(243 / 64) := by norm_num only
  rw [h, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith only [hr]

private theorem principal_coeff_upper : gaussianK131RhCoeff ≤ 14411 / 1000000 := by
  rw [gaussianK131RhCoeff, gaussianK131UnitWeight, k131_amplitude_eq, inverse_at_edge]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  linarith only [exp_edge_upper]

private theorem principal_error_lower {y a b c d : ℝ} (h : 2 * Real.log y ∈ Set.Icc a b)
    (h' : Real.log (2 * Real.log y) ∈ Set.Icc c d) (ha : 0 ≤ a) (hsub : d ≤ a) :
    -(14411 / 1000000 : ℝ) * (b * (b - c)) ≤ k131PrincipalError gaussianK131RhCoeff y := by
  unfold k131PrincipalError
  have hl : 0 ≤ 2 * Real.log y := ha.trans h.1
  have hd : 0 ≤ 2 * Real.log y - Real.log (2 * Real.log y) :=
    sub_nonneg.mpr (h'.2.trans (hsub.trans h.1))
  have hm := mul_le_mul h.2 (sub_le_sub h.2 h'.1) hd (hl.trans h.2)
  have hb : 0 ≤ b * (b - c) := (mul_nonneg hl hd).trans hm
  have hc := mul_le_mul principal_coeff_upper hm (mul_nonneg hl hd) (by norm_num only)
  linarith only [hc]

/-- A rational lower bound on the principal RH error at the left K131 endpoint. -/
theorem k131_left_principal_lower :
    -(233425 / 100000 : ℝ) ≤ k131PrincipalError gaussianK131RhCoeff (465644807 / 400000) := by
  refine
    le_trans ?_
      (principal_error_lower k131_left_log_bounds k131_left_log_log_bounds (by norm_num only)
        (by norm_num only))
  norm_num only

/-- A rational lower bound on the principal RH error at the right K131 endpoint. -/
theorem k131_right_principal_lower :
    -(332423 / 100000 : ℝ) ≤ k131PrincipalError gaussianK131RhCoeff (1036273 / 250) := by
  refine
    le_trans ?_
      (principal_error_lower k131_right_log_bounds k131_right_log_log_bounds (by norm_num only)
        (by norm_num only))
  norm_num only

private theorem monomial_moment (a c : ℝ) (ha : 0 < a) (k : ℕ) :
    (∫ x in (0 : ℝ)..9 / 4, Real.exp (-a * x) * (c * x ^ k)) =
      c *
        (Analysis.logPowerTailPoly a k 0 -
          Real.exp (-a * (9 / 4)) * Analysis.logPowerTailPoly a k (9 / 4)) := by
  have he :
    (fun x : ℝ ↦ Real.exp (-a * x) * (c * x ^ k)) = fun x ↦ c * (x ^ k * Real.exp (-a * x)) := by
    funext x
    ring
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num only)]
  exact congrArg (fun z : ℝ ↦ c * z) (Analysis.exponential_moment_interval ha (by norm_num only) k)

private theorem k131_moment_eval (a : ℝ) (ha : 0 < a) :
    gaussianK131Moment a =
      ∑ j : Fin 9,
        (inverseCoeffs j : ℝ) *
          (Analysis.logPowerTailPoly a (2 * j.val + 3) 0 -
            Real.exp (-a * (9 / 4)) * Analysis.logPowerTailPoly a (2 * j.val + 3) (9 / 4)) := by
  simp only [gaussianK131Moment, gaussianK131Inverse, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · exact Finset.sum_congr rfl (fun j _ ↦ monomial_moment a _ ha (2 * j.val + 3))
  · intro j _
    apply Continuous.intervalIntegrable
    exact
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.mul (continuous_id.pow _))

private def tailRat (a : ℚ) : ℕ → ℚ → ℚ
  | 0, _ => 1 / a
  | k + 1, z => z ^ (k + 1) / a + ((k + 1 : ℕ) : ℚ) / a * tailRat a k z

private theorem cast_tail_rat (a z : ℚ) (k : ℕ) :
    (tailRat a k z : ℝ) = Analysis.logPowerTailPoly (a : ℝ) k (z : ℝ) := by
  induction k with
  | zero => simp only [tailRat, Analysis.logPowerTailPoly, Rat.cast_div, Rat.cast_one]
  | succ k ih =>
    simp only [tailRat, Analysis.logPowerTailPoly, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_natCast, ih]

private theorem eval_iterate_inverse (d : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[d]) gaussianK131InversePoly).eval x =
      ∑ j : Fin 9,
        (inverseCoeffs j : ℝ) *
          (((2 * j.val + 3).descFactorial d : ℝ) * x ^ (2 * j.val + 3 - d)) := by
  have hmono (n : ℕ) (c : ℝ) :
    (Polynomial.derivative^[d]) (Polynomial.monomial n c) =
      Polynomial.C c * ((n.descFactorial d : ℝ) • Polynomial.X ^ (n - d)) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.iterate_derivative_C_mul]
    simpa only [map_zero, sub_zero, ← Nat.cast_smul_eq_nsmul ℝ] using
      congrArg (fun P : Polynomial ℝ ↦ Polynomial.C c * P)
        (Polynomial.iterate_derivative_X_sub_pow n d (0 : ℝ))
  simp only [gaussianK131InversePoly, Polynomial.iterate_derivative_sum, hmono,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_smul]
  rfl

private theorem eval_inverse_moment (a x : ℝ) (m : ℕ) :
    (k131MomentPoly gaussianK131InversePoly a m).eval x =
      ∑ d ∈ Finset.range 20,
        (((d + m).factorial : ℝ) / (d.factorial : ℝ) / a ^ (d + m + 1)) *
          ∑ j : Fin 9,
            (inverseCoeffs j : ℝ) *
              (((2 * j.val + 3).descFactorial d : ℝ) * x ^ (2 * j.val + 3 - d)) := by
  simp only [k131MomentPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    eval_iterate_inverse]

private theorem eval_gamma_moment (a x : ℝ) (m : ℕ) :
    (k131MomentPoly (gammaMainPoly gaussianK131InversePoly) a m).eval x =
      ∑ d ∈ Finset.range 20,
        (((d + m).factorial : ℝ) / (d.factorial : ℝ) / a ^ (d + m + 1)) *
          ((35 / 16) * ((Polynomial.derivative^[d]) gaussianK131InversePoly).eval x -
            ((Polynomial.derivative^[d + 1]) gaussianK131InversePoly).eval x) := by
  simp only [k131MomentPoly, gammaMainPoly, Polynomial.iterate_derivative_sub,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_finsetSum, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Function.iterate_succ_apply]

private theorem eval_reflect_moment (a x : ℝ) (m : ℕ) (j : Fin 2) :
    (reflectPoly (k131MomentPoly gaussianK131InversePoly a m) j).eval x =
      ∑ d ∈ Finset.range 20,
        (((d + m).factorial : ℝ) / (d.factorial : ℝ) / a ^ (d + m + 1)) *
          ∑ i : Fin 9,
            (inverseCoeffs i : ℝ) *
              (((2 * i.val + 3).descFactorial d : ℝ) *
                (2 * x - reflectionOffsets j) ^ (2 * i.val + 3 - d)) := by
  simp only [reflectPoly, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, eval_inverse_moment]

private theorem eval_reflection_23 (x : ℝ) :
    gaussianK131Poly23.eval x =
      ∑ j : Fin 2,
        reflectFactor j *
          (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval
            (2 * x - reflectionOffsets j) := by
  simp only [gaussianK131Poly23, reflectPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X]

private theorem eval_reflection_higher (x : ℝ) :
    gaussianK131PolyHigher.eval x =
      ∑ j : Fin 2,
        let v := 2 * x - reflectionOffsets j
        let M m := (k131MomentPoly (gammaMainPoly gaussianK131InversePoly) (27 / 16) m).eval v
        (reflectFactor j / 24) * (x ^ 2 * (gaussianK131Inverse v + M 0) + 2 * x * M 1 + M 2) := by
  simp only [gaussianK131PolyHigher, reflectPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_add, gaussian_k131_inverse_eval]

private def inverseMomentRat (a z : ℚ) (m : ℕ := 0) : ℚ :=
  ∑ d ∈ Finset.range 20,
    (((d + m).factorial : ℚ) / (d.factorial : ℚ) / a ^ (d + m + 1)) *
      ∑ j : Fin 9,
        inverseCoeffs j * (((2 * j.val + 3).descFactorial d : ℚ) * z ^ (2 * j.val + 3 - d))

private theorem inverse_moment_upper (a z : ℚ) {x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hz : x ≤ (z : ℝ))
    (m : ℕ := 0) :
    (k131MomentPoly gaussianK131InversePoly (a : ℝ) m).eval x ≤ (inverseMomentRat a z m : ℝ) := by
  rw [eval_inverse_moment]
  simp only [inverseMomentRat, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_div]
  apply Finset.sum_le_sum
  intro d _
  apply
    mul_le_mul_of_nonneg_left _
      (div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr ha.le) _))
  apply Finset.sum_le_sum
  intro j _
  have hc : ∀ i : Fin 9, 0 ≤ inverseCoeffs i := by decide +kernel
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hz _) (Nat.cast_nonneg _))
      ((Rat.cast_nonneg (K := ℝ)).mpr (hc j))

private theorem left_short_moment_upper {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 2814 / 100) :
    (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval x ≤ 180000000000000 := by
  have hq : inverseMomentRat (19 / 16) (2814 / 100) ≤ 180000000000000 := by decide +kernel
  have h := (Rat.cast_le (K := ℝ)).mpr hq
  have hm :=
    inverse_moment_upper (19 / 16) (2814 / 100) (by decide +kernel) hx
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hu)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hm.trans h

private theorem left_long_moment_upper {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 2374 / 100) :
    (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval x ≤ 9400000000000 := by
  have hq : inverseMomentRat (19 / 16) (2374 / 100) ≤ 9400000000000 := by decide +kernel
  have h := (Rat.cast_le (K := ℝ)).mpr hq
  have hm :=
    inverse_moment_upper (19 / 16) (2374 / 100) (by decide +kernel) hx
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hu)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hm.trans h

private theorem right_moment_upper (z M : ℚ) {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ (z : ℝ))
    (hM : inverseMomentRat (19 / 16) z ≤ M) :
    (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval x ≤ (M : ℝ) := by
  have h := inverse_moment_upper (19 / 16) z (by decide +kernel) hx hu
  have he : ((19 / 16 : ℚ) : ℝ) = 19 / 16 := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [he] at h
  exact h.trans ((Rat.cast_le (K := ℝ)).mpr hM)

private theorem reflect_factor_short_lower : -(28 / 1000 : ℝ) ≤ reflectFactor 0 := by
  change
    _ ≤
      -4 * (973 / 5000 - 1831 / 10000 * Real.exp (-(27 / 16 : ℝ) * (1 / 10))) *
        (gaussianK131Amplitude : ℝ) *
        Real.exp ((27 / 16 : ℝ) * (1 / 10))
  rw [k131_amplitude_eq]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have he : Real.exp (0.16875 : ℝ) ≤ 1.184 := by dyadic_interval [prec := 24]
  have he' : Real.exp ((27 / 16 : ℝ) * (1 / 10)) ≤ 1.184 := by
    convert he using 2
    norm_num only
  have h : Real.exp (-(27 / 16 : ℝ) * (1 / 10)) * Real.exp ((27 / 16 : ℝ) * (1 / 10)) = 1 := by
    rw [← Real.exp_add]
    norm_num only [Real.exp_zero]
  nlinarith only [he', h]

private theorem reflect_factor_long_lower : -(116 / 10 : ℝ) ≤ reflectFactor 1 := by
  change
    _ ≤
      -4 * (13 / 1250 - 1 / 80 * Real.exp (-(27 / 16 : ℝ) * (12 / 5))) *
        (gaussianK131Amplitude : ℝ) *
        Real.exp ((27 / 16 : ℝ) * (9 / 2))
  rw [k131_amplitude_eq]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have he : Real.exp (7.59375 : ℝ) ≤ 1986 := by dyadic_interval [prec := 26]
  have hb : (34 : ℝ) ≤ Real.exp 3.54375 := by dyadic_interval [prec := 26]
  have he' : Real.exp ((27 / 16 : ℝ) * (9 / 2)) ≤ 1986 := by
    convert he using 2
    norm_num only
  have h :
    Real.exp (-(27 / 16 : ℝ) * (12 / 5)) * Real.exp ((27 / 16 : ℝ) * (9 / 2)) =
      Real.exp 3.54375 := by
    rw [← Real.exp_add]
    congr 1
    norm_num only
  nlinarith only [he', hb, h]

private theorem left_poly23_lower :
    -(115000000000000 : ℝ) ≤ gaussianK131Poly23.eval (2 * Real.log (465644807 / 400000)) := by
  let x := 2 * Real.log (465644807 / 400000)
  have hx := k131_left_log_bounds
  change x ∈ Set.Icc _ _ at hx
  have hs :=
    left_short_moment_upper (x := 2 * x - 1 / 10) (by linarith only [hx.1])
      (by linarith only [hx.2])
  have hl :=
    left_long_moment_upper (x := 2 * x - 9 / 2) (by linarith only [hx.1]) (by linarith only [hx.2])
  have h₁ := mul_le_mul_of_nonpos_left hs (reflect_factor_nonpos 0)
  have h₂ := mul_le_mul_of_nonpos_left hl (reflect_factor_nonpos 1)
  change _ ≤ gaussianK131Poly23.eval x
  rw [eval_reflection_23, Fin.sum_univ_two]
  change
    _ ≤
      reflectFactor 0 * (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval (2 * x - 1 / 10) +
        reflectFactor 1 * (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval (2 * x - 9 / 2)
  linarith only [h₁, h₂, reflect_factor_short_lower, reflect_factor_long_lower]

/-- The contribution with exponent 23/4 at the left K131 endpoint is
bounded below by -0.00028 using the reflected moment bounds. -/
theorem k131_left_reflect23_lower :
    let y : ℝ := 465644807 / 400000
    (-(28 / 100000 : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 6) * (gaussianK131GapPoly 6).eval (2 * Real.log y)) := by
  let y : ℝ := 465644807 / 400000
  let r := y ^ (1 / 8 : ℝ)
  let a : ℝ := 24168480494 / 10000000000
  have ha : 0 < a := by
    dsimp only [a]; norm_num only
  have hr : a ≤ r := k131_left_root_bounds.1
  have hi : (r ^ (46 : ℕ))⁻¹ ≤ (a ^ (46 : ℕ))⁻¹ :=
    inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hr _)
  change _ ≤ r ^ (-46 : ℤ) * gaussianK131Poly23.eval _
  rw [zpow_neg, zpow_ofNat]
  have h :=
    mul_le_mul_of_nonneg_left left_poly23_lower (inv_nonneg.mpr (pow_nonneg (ha.le.trans hr) 46))
  have h' := mul_le_mul_of_nonpos_left hi (by norm_num only : -(115000000000000 : ℝ) ≤ 0)
  dsimp only [a] at h'
  linarith only [h, h']

private theorem right_poly23_lower :
    -(3300000000000000 : ℝ) ≤ gaussianK131Poly23.eval (2 * Real.log (1036273 / 250)) := by
  let x := 2 * Real.log (1036273 / 250)
  have hx := k131_right_log_bounds
  change x ∈ Set.Icc _ _ at hx
  have hs :=
    right_moment_upper (3322 / 100) 3440000000000000 (x := 2 * x - 1 / 10) (by linarith only [hx.1])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by decide +kernel)
  have hl :=
    right_moment_upper (2882 / 100) 274000000000000 (x := 2 * x - 9 / 2) (by linarith only [hx.1])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by decide +kernel)
  have h₁ := mul_le_mul_of_nonpos_left hs (reflect_factor_nonpos 0)
  have h₂ := mul_le_mul_of_nonpos_left hl (reflect_factor_nonpos 1)
  change _ ≤ gaussianK131Poly23.eval x
  rw [eval_reflection_23, Fin.sum_univ_two]
  change
    _ ≤
      reflectFactor 0 * (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval (2 * x - 1 / 10) +
        reflectFactor 1 * (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval (2 * x - 9 / 2)
  norm_num only [Rat.cast_ofNat] at h₁ h₂
  linarith only [h₁, h₂, reflect_factor_short_lower, reflect_factor_long_lower]

/-- The contribution with exponent 23/4 at the right K131 endpoint is
bounded below by -0.000006 using the reflected moment bounds. -/
theorem k131_right_reflect23_lower :
    let y : ℝ := 1036273 / 250
    (-(6 / 1000000 : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 6) * (gaussianK131GapPoly 6).eval (2 * Real.log y)) := by
  let y : ℝ := 1036273 / 250
  let r := y ^ (1 / 8 : ℝ)
  let a : ℝ := 28326425319 / 10000000000
  have ha : 0 < a := by
    dsimp only [a]; norm_num only
  have hr : a ≤ r := k131_right_root_bounds.1
  have hi : (r ^ (46 : ℕ))⁻¹ ≤ (a ^ (46 : ℕ))⁻¹ :=
    inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hr _)
  change _ ≤ r ^ (-46 : ℤ) * gaussianK131Poly23.eval _
  rw [zpow_neg, zpow_ofNat]
  have h :=
    mul_le_mul_of_nonneg_left right_poly23_lower (inv_nonneg.mpr (pow_nonneg (ha.le.trans hr) 46))
  have h' := mul_le_mul_of_nonpos_left hi (by norm_num only : -(3300000000000000 : ℝ) ≤ 0)
  dsimp only [a] at h'
  linarith only [h, h']

private theorem exp_recovery_lower :
    (3938481 / 100000000 : ℝ) ≤ Real.exp (-(23 / 16) * (9 / 4)) := by
  have hu :=
    Analysis.exp_le_taylor_ratio (x := 207 / 64) (q := 1 / 2) (n := 24) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)
  have hq :
    Analysis.gammaPositiveTaylor (207 / 64) 24 +
        (207 / 64 : ℚ) ^ 24 / (24 : ℕ).factorial / (1 - 1 / 2) ≤
      100000000 / 3938481 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  simp only [Analysis.gammaPositiveTaylor, Rat.cast_sum, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat] at hr
  have he : -(23 / 16 : ℝ) * (9 / 4) = -(207 / 64) := by norm_num only
  rw [he, Real.exp_neg, inv_eq_one_div, le_div_iff₀ (Real.exp_pos _)]
  linarith only [hu.trans hr]

private theorem recovery_moment_upper : gaussianK131Moment (23 / 16) ≤ 331 / 500 := by
  rw [k131_moment_eval _ (by norm_num only)]
  have hq :
    (∑ j : Fin 9,
        inverseCoeffs j *
          (tailRat (23 / 16) (2 * j.val + 3) 0 -
            (3938481 / 100000000) * tailRat (23 / 16) (2 * j.val + 3) (9 / 4))) ≤
      (331 / 500 : ℚ) := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr hq
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, cast_tail_rat, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_zero] at hr
  refine le_trans ?_ hr
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (Rat.cast_nonneg.mpr ?_)
  · exact
      sub_le_sub_left
        (mul_le_mul_of_nonneg_right exp_recovery_lower
          (Analysis.log_power_tail_poly_nonneg (by norm_num only) (by norm_num only) _))
        _
  · have h : ∀ k : Fin 9, 0 ≤ inverseCoeffs k := by decide +kernel
    exact h j

private theorem exp_nine_sixteenths_upper : Real.exp (-(9 / 16 : ℝ)) ≤ 57 / 100 := by
  have hr : (100 / 57 : ℝ) ≤ Real.exp (9 / 16) := by
    have hq : (100 / 57 : ℚ) ≤ Analysis.gammaPositiveTaylor (9 / 16) 8 := by decide +kernel
    have h :=
      ((Rat.cast_le (K := ℝ)).mpr hq).trans
        (Analysis.gamma_positive_taylor_le_exp (by norm_num only) 8)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using h
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith only [hr]

private theorem unit_weight_upper : gaussianK131UnitWeight ≤ 90546 / 1000000 := by
  rw [gaussianK131UnitWeight, k131_amplitude_eq, inverse_at_edge]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  linarith only [exp_edge_upper]

private theorem recovery_variation_upper : gaussianK131RecoveryVariation ≤ 779 / 1000 := by
  unfold gaussianK131RecoveryVariation
  have ha : (gaussianK131Amplitude : ℝ) ≤ 144 / 1000 := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hm := moment_nonneg (23 / 16)
  have he := mul_le_mul exp_nine_sixteenths_upper recovery_moment_upper hm (by norm_num only)
  have h := mul_le_mul ha he (mul_nonneg (Real.exp_pos _).le hm) (by norm_num only)
  rw [← mul_assoc] at h
  linarith only [unit_weight_upper, h]

private theorem recovery_lower {r a : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    -(81 / 100 : ℝ) * (779 / 1000) / a ^ (4 : ℕ) ≤
      r ^ (-4 : ℤ) * (-((81 / 100 : ℝ) * gaussianK131RecoveryVariation)) := by
  have hinv : (r ^ (4 : ℕ))⁻¹ ≤ (a ^ (4 : ℕ))⁻¹ :=
    inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hr _)
  have h :=
    mul_le_mul hinv recovery_variation_upper gaussian_k131_recovery_nonneg
      (inv_nonneg.mpr (pow_nonneg ha.le _))
  rw [zpow_neg, zpow_ofNat]
  simp only [div_eq_mul_inv] at *
  linarith only [h]

/-- A rational lower bound on the square-recovery term at the left endpoint. -/
theorem k131_left_recovery_lower :
    -(185 / 10000 : ℝ) ≤
      ((465644807 / 400000 : ℝ) ^ (1 / 8 : ℝ)) ^ (-4 : ℤ) *
        (-((81 / 100 : ℝ) * gaussianK131RecoveryVariation)) := by
  refine le_trans ?_ (recovery_lower (by norm_num only) k131_left_root_bounds.1)
  norm_num only

/-- A rational lower bound on the square-recovery term at the right endpoint. -/
theorem k131_right_recovery_lower :
    -(981 / 100000 : ℝ) ≤
      ((1036273 / 250 : ℝ) ^ (1 / 8 : ℝ)) ^ (-4 : ℤ) *
        (-((81 / 100 : ℝ) * gaussianK131RecoveryVariation)) := by
  refine le_trans ?_ (recovery_lower (by norm_num only) k131_right_root_bounds.1)
  norm_num only

/-- The contribution from the eight power-polynomial terms in the
endpoint comparison. The principal and recovery errors are accounted for separately. -/
noncomputable def k131EndpointPolynomialSum (y : ℝ) : ℝ :=
  ∑ j : Fin 8, (y ^ (1 / 8 : ℝ)) ^ (k131GapPower j) * (gaussianK131GapPoly j).eval (2 * Real.log y)

/-- A lower estimate on the eight polynomial terms suffices for the
required left endpoint gap, using the verified error bounds above. -/
theorem k131_left_gap_of_polynomials
    (h : (235775 / 100000 : ℝ) < k131EndpointPolynomialSum (465644807 / 400000)) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  rw [k131_gap_eval_root (by norm_num only)]
  unfold k131EndpointPolynomialSum at h
  have hp := k131_left_principal_lower
  unfold k131PrincipalError at hp
  linarith only [h, hp, k131_left_recovery_lower]

/-- A lower estimate on the eight polynomial terms suffices for the
required right endpoint gap, using the verified error bounds above. -/
theorem k131_right_gap_of_polynomials
    (h : (333904 / 100000 : ℝ) < k131EndpointPolynomialSum (1036273 / 250)) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  rw [k131_gap_eval_root (by norm_num only)]
  unfold k131EndpointPolynomialSum at h
  have hp := k131_right_principal_lower
  unfold k131PrincipalError at hp
  linarith only [h, hp, k131_right_recovery_lower]

private theorem endpoint_edge_loss_upper : gaussianK131EdgeLoss ≤ 26 / 125 := by
  rw [gaussianK131EdgeLoss, k131_amplitude_eq, inverse_at_edge, inverse_derivative_at_edge]
  simp only [Rat.cast_div, Rat.cast_ofNat]
  rw [abs_of_nonpos (by norm_num only)]
  linarith only [exp_edge_upper]

private theorem endpoint_reciprocal_lower : (7603577 / 100000 : ℝ) ≤ gaussianK131Reciprocal := by
  have hg : gammaIntegralZero = 16137535984833796448326844416 / 37589973457545958193355601 := by
    decide +kernel
  rw [gaussianK131Reciprocal, gaussianK131UnitWeight, inverse_at_edge, hg]
  have h₁ : (1.051271096 : ℝ) ≤ Real.exp 0.05 := by dyadic_interval [prec := 45]
  have h₂ : Real.exp (1.05 : ℝ) ≤ 2.857651119 := by dyadic_interval [prec := 45]
  have h₃ : (9.487735836 : ℝ) ≤ Real.exp 2.25 := by dyadic_interval [prec := 45]
  have h₄ : (0.324652467 : ℝ) ≤ Real.exp (-1.125) := by dyadic_interval [prec := 45]
  have h₅ : (0.022440789 : ℝ) ≤ Real.exp (-3.796875) := by dyadic_interval [prec := 45]
  have e₁ : (0.05 : ℝ) = 1 / 20 := by norm_num only
  have e₂ : (1.05 : ℝ) = 21 / 20 := by norm_num only
  have e₃ : (2.25 : ℝ) = 9 / 4 := by norm_num only
  have e₄ : (-1.125 : ℝ) = -(9 / 8) := by norm_num only
  have e₅ : (-3.796875 : ℝ) = -(27 / 16) * (9 / 4) := by norm_num only
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  rw [e₄] at h₄
  rw [e₅] at h₅
  simp only [negativePole, k131_amplitude_eq, kernelNumerator, reciprocalLogLower, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_mul, Rat.cast_add, Rat.cast_pow]
  linarith only [h₁, h₂, h₃, h₄, h₅]

private theorem endpoint_reciprocal_term (y : ℝ) (hy : 0 < y) :
    (7603577 / 100000 : ℝ) / y ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 2) * (gaussianK131GapPoly 2).eval (2 * Real.log y) := by
  change _ ≤ (y ^ (1 / 8 : ℝ)) ^ (-8 : ℤ) * (Polynomial.C gaussianK131Reciprocal).eval _
  rw [← k131_rpow_eighth hy.le, Polynomial.eval_C]
  norm_num only [Int.cast_neg, Int.cast_ofNat, neg_div, div_self (by norm_num only : (8 : ℝ) ≠ 0),
    Real.rpow_neg_one, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right endpoint_reciprocal_lower hy.le

private theorem endpoint_edge_term (y : ℝ) (hy : 1000 ≤ y) :
    -(1 / 10 ^ (14 : ℕ) : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 5) * (gaussianK131GapPoly 5).eval (2 * Real.log y) := by
  have hy₀ : 0 < y := (by norm_num only : (0 : ℝ) < 1000).trans_le hy
  change _ ≤ (y ^ (1 / 8 : ℝ)) ^ (-40 : ℤ) * (Polynomial.C (-gaussianK131EdgeLoss)).eval _
  rw [← k131_rpow_eighth hy₀.le, Polynomial.eval_C]
  have h : ((-40 : ℤ) : ℝ) / 8 = -(5 : ℝ) := by norm_num only
  rw [h, Real.rpow_neg hy₀.le, ← Nat.cast_ofNat (R := ℝ) (n := 5), Real.rpow_natCast]
  have hi : (y ^ (5 : ℕ))⁻¹ ≤ ((1000 : ℝ) ^ (5 : ℕ))⁻¹ :=
    inv_anti₀ (by norm_num only) (pow_le_pow_left₀ (by norm_num only) hy _)
  have he :=
    mul_le_mul hi endpoint_edge_loss_upper
      (by
        unfold gaussianK131EdgeLoss
        rw [k131_amplitude_eq]
        positivity)
      (by norm_num only)
  linarith only [he]

/-- The reciprocal-radius and fifth-power terms at the left endpoint
contribute at least 0.0653 to the polynomial sum. -/
theorem k131_left_constant_losses :
    let y : ℝ := 465644807 / 400000
    let r := y ^ (1 / 8 : ℝ)
    (653 / 10000 : ℝ) ≤
      r ^ (k131GapPower 2) * (gaussianK131GapPoly 2).eval (2 * Real.log y) +
        r ^ (k131GapPower 5) * (gaussianK131GapPoly 5).eval (2 * Real.log y) := by
  have hr := endpoint_reciprocal_term (465644807 / 400000) (by norm_num only)
  have he := endpoint_edge_term (465644807 / 400000) (by norm_num only)
  dsimp only
  linarith only [hr, he]

/-- The reciprocal-radius and fifth-power terms at the right endpoint
contribute at least 0.01834 to the polynomial sum. -/
theorem k131_right_constant_losses :
    let y : ℝ := 1036273 / 250
    let r := y ^ (1 / 8 : ℝ)
    (1834 / 100000 : ℝ) ≤
      r ^ (k131GapPower 2) * (gaussianK131GapPoly 2).eval (2 * Real.log y) +
        r ^ (k131GapPower 5) * (gaussianK131GapPoly 5).eval (2 * Real.log y) := by
  have hr := endpoint_reciprocal_term (1036273 / 250) (by norm_num only)
  have he := endpoint_edge_term (1036273 / 250) (by norm_num only)
  dsimp only
  linarith only [hr, he]

/-- Sum of the six endpoint terms whose coefficients still depend on the
Fourier, inverse Mellin and reflection polynomials. -/
noncomputable def k131EndpointSixTerms (y : ℝ) : ℝ :=
  ∑ j ∈ ((Finset.univ : Finset (Fin 8)).erase 5).erase 2,
    (y ^ (1 / 8 : ℝ)) ^ (k131GapPower j) * (gaussianK131GapPoly j).eval (2 * Real.log y)

private theorem endpoint_split (y : ℝ) :
    k131EndpointPolynomialSum y =
      k131EndpointSixTerms y +
        ((y ^ (1 / 8 : ℝ)) ^ (k131GapPower 2) * (gaussianK131GapPoly 2).eval (2 * Real.log y) +
          (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 5) *
            (gaussianK131GapPoly 5).eval (2 * Real.log y)) := by
  let f : Fin 8 → ℝ := fun j ↦
    (y ^ (1 / 8 : ℝ)) ^ (k131GapPower j) * (gaussianK131GapPoly j).eval (2 * Real.log y)
  change (∑ j, f j) = (∑ j ∈ ((Finset.univ : Finset (Fin 8)).erase 5).erase 2, f j) + _
  rw [← add_assoc, Finset.sum_erase_add _ _ (by decide), Finset.sum_erase_add _ _ (by decide)]

/-- The six remaining terms need a lower bound of 2.29245 at the left
endpoint once the other two terms and both error bounds are included. -/
theorem k131_left_gap_of_six
    (h : (229245 / 100000 : ℝ) < k131EndpointSixTerms (465644807 / 400000)) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  apply k131_left_gap_of_polynomials
  rw [endpoint_split]
  linarith only [h, k131_left_constant_losses]

/-- The six remaining terms need a lower bound of 3.32070 at the right
endpoint once the other two terms and both error bounds are included. -/
theorem k131_right_gap_of_six (h : (332070 / 100000 : ℝ) < k131EndpointSixTerms (1036273 / 250)) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  apply k131_right_gap_of_polynomials
  rw [endpoint_split]
  linarith only [h, k131_right_constant_losses]

/-- After accounting for the lower reflection term, the five remaining
polynomial terms at the left endpoint need to exceed 2.29273. -/
theorem k131_left_gap_of_five
    (h :
      (229273 / 100000 : ℝ) <
        ∑ j ∈ (((Finset.univ : Finset (Fin 8)).erase 5).erase 2).erase 6,
          ((465644807 / 400000 : ℝ) ^ (1 / 8 : ℝ)) ^ (k131GapPower j) *
            (gaussianK131GapPoly j).eval (2 * Real.log (465644807 / 400000))) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  apply k131_left_gap_of_six
  unfold k131EndpointSixTerms
  rw [← Finset.sum_erase_add _ _ (by decide : (6 : Fin 8) ∈ (Finset.univ.erase 5).erase 2)]
  linarith only [h, k131_left_reflect23_lower]

/-- After accounting for the lower reflection term, the five remaining
polynomial terms at the right endpoint need to exceed 3.320706. -/
theorem k131_right_gap_of_five
    (h :
      (3320706 / 1000000 : ℝ) <
        ∑ j ∈ (((Finset.univ : Finset (Fin 8)).erase 5).erase 2).erase 6,
          ((1036273 / 250 : ℝ) ^ (1 / 8 : ℝ)) ^ (k131GapPower j) *
            (gaussianK131GapPoly j).eval (2 * Real.log (1036273 / 250))) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  apply k131_right_gap_of_six
  unfold k131EndpointSixTerms
  rw [← Finset.sum_erase_add _ _ (by decide : (6 : Fin 8) ∈ (Finset.univ.erase 5).erase 2)]
  linarith only [h, k131_right_reflect23_lower]

private theorem inverse_iterate_nonneg (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ((Polynomial.derivative^[d]) gaussianK131InversePoly).eval x := by
  rw [eval_iterate_inverse]
  apply Finset.sum_nonneg
  intro j _
  have hc : ∀ i : Fin 9, 0 ≤ inverseCoeffs i := by decide +kernel
  exact
    mul_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr (hc j))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _))

private theorem gamma_moment_le_inverse {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (m : ℕ) :
    (k131MomentPoly (gammaMainPoly gaussianK131InversePoly) a m).eval x ≤
      (35 / 16) * (k131MomentPoly gaussianK131InversePoly a m).eval x := by
  rw [eval_gamma_moment, eval_inverse_moment, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  rw [← eval_iterate_inverse]
  let w : ℝ := (d + m).factorial / (d.factorial : ℝ) / a ^ (d + m + 1)
  let v := ((Polynomial.derivative^[d]) gaussianK131InversePoly).eval x
  have hw : 0 ≤ w :=
    div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg ha.le _)
  change w * ((35 / 16) * v - _) ≤ (35 / 16) * (w * v)
  calc
    _ ≤ w * ((35 / 16) * v) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (inverse_iterate_nonneg _ hx)) hw
    _ = _ := by ring

private def inverseEvalRat (z : ℚ) : ℚ :=
  ∑ j : Fin 9, inverseCoeffs j * z ^ (2 * j.val + 3)

private theorem inverse_eval_upper {v : ℝ} (z : ℚ) (hv : 0 ≤ v) (hz : v ≤ (z : ℝ)) :
    gaussianK131Inverse v ≤ (inverseEvalRat z : ℝ) := by
  simp only [gaussianK131Inverse, inverseEvalRat, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]
  apply Finset.sum_le_sum
  intro j _
  have h : ∀ i : Fin 9, 0 ≤ inverseCoeffs i := by decide +kernel
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hz _) ((Rat.cast_nonneg (K := ℝ)).mpr (h j))

private theorem inverse_moment_rat_nonneg {z : ℚ} (hz : 0 ≤ z) (m : ℕ) :
    0 ≤ inverseMomentRat (27 / 16) z m := by
  unfold inverseMomentRat
  apply Finset.sum_nonneg
  intro d _
  refine
    mul_nonneg
      (div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg (by norm_num only) _))
      (Finset.sum_nonneg ?_)
  intro j _
  have h : ∀ i : Fin 9, 0 ≤ inverseCoeffs i := by decide +kernel
  exact mul_nonneg (h j) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))

private def higherBracketRat (X z : ℚ) : ℚ :=
  let M m := (35 / 16) * inverseMomentRat (27 / 16) z m
  X ^ 2 * (inverseEvalRat z + M 0) + 2 * X * M 1 + M 2

private theorem higher_bracket_upper {x v : ℝ} (X z : ℚ) (hx : 0 ≤ x) (hX : x ≤ (X : ℝ))
    (hv : 0 ≤ v) (hz : v ≤ (z : ℝ)) :
    let M m := (k131MomentPoly (gammaMainPoly gaussianK131InversePoly) (27 / 16) m).eval v
    x ^ 2 * (gaussianK131Inverse v + M 0) + 2 * x * M 1 + M 2 ≤ (higherBracketRat X z : ℝ) := by
  let U m : ℝ := (35 / 16) * (inverseMomentRat (27 / 16) z m : ℝ)
  have hU m : 0 ≤ U m :=
    mul_nonneg (by norm_num only)
      ((Rat.cast_nonneg (K := ℝ)).mpr
        (inverse_moment_rat_nonneg ((Rat.cast_nonneg (K := ℝ)).mp (hv.trans hz)) m))
  have hI : 0 ≤ (inverseEvalRat z : ℝ) := (inverse_nonneg hv).trans (inverse_eval_upper z hv hz)
  have hM m :
    (k131MomentPoly (gammaMainPoly gaussianK131InversePoly) (27 / 16) m).eval v ≤ U m := by
    have h := inverse_moment_upper (27 / 16) z (by norm_num only) hv hz m
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact
      (gamma_moment_le_inverse (by norm_num only) hv m).trans
        (mul_le_mul_of_nonneg_left h (by norm_num only))
  simp only [higherBracketRat, Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_div,
    Rat.cast_ofNat]
  change _ ≤ (X : ℝ) ^ 2 * ((inverseEvalRat z : ℝ) + U 0) + 2 * (X : ℝ) * U 1 + U 2
  apply add_le_add (add_le_add _ _) (hM 2)
  · exact
      (mul_le_mul_of_nonneg_left (add_le_add (inverse_eval_upper z hv hz) (hM 0))
            (sq_nonneg x)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hX _) (add_nonneg hI (hU 0)))
  · exact
      (mul_le_mul_of_nonneg_left (hM 1) (mul_nonneg (by norm_num only) hx)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by norm_num only)) (hU 1))

private theorem higher_eval_lower {x : ℝ} (X z₀ z₁ C₀ C₁ : ℚ) (hx : 9 / 4 ≤ x) (hX : x ≤ (X : ℝ))
    (hz₀ : 2 * x - 1 / 10 ≤ (z₀ : ℝ)) (hz₁ : 2 * x - 9 / 2 ≤ (z₁ : ℝ))
    (h₀ : higherBracketRat X z₀ ≤ C₀) (h₁ : higherBracketRat X z₁ ≤ C₁) (hc₀ : 0 ≤ C₀)
    (hc₁ : 0 ≤ C₁) :
    -(28 / 1000 : ℝ) / 24 * (C₀ : ℝ) - (116 / 10 : ℝ) / 24 * (C₁ : ℝ) ≤
      gaussianK131PolyHigher.eval x := by
  have b₀ :=
    (higher_bracket_upper X z₀ (by linarith only [hx]) hX (by linarith only [hx]) hz₀).trans
      ((Rat.cast_le (K := ℝ)).mpr h₀)
  have b₁ :=
    (higher_bracket_upper X z₁ (by linarith only [hx]) hX (by linarith only [hx]) hz₁).trans
      ((Rat.cast_le (K := ℝ)).mpr h₁)
  have h₂ :=
    mul_le_mul_of_nonpos_left b₀
      (div_nonpos_of_nonpos_of_nonneg (reflect_factor_nonpos 0) (by norm_num only : (0 : ℝ) ≤ 24))
  have h₃ :=
    mul_le_mul_of_nonpos_left b₁
      (div_nonpos_of_nonpos_of_nonneg (reflect_factor_nonpos 1) (by norm_num only : (0 : ℝ) ≤ 24))
  have h₄ :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right reflect_factor_short_lower (by norm_num only : (0 : ℝ) ≤ 24))
      ((Rat.cast_nonneg (K := ℝ)).mpr hc₀)
  have h₅ :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right reflect_factor_long_lower (by norm_num only : (0 : ℝ) ≤ 24))
      ((Rat.cast_nonneg (K := ℝ)).mpr hc₁)
  rw [eval_reflection_higher, Fin.sum_univ_two]
  exact le_trans (by linarith only [h₄, h₅]) (add_le_add h₂ h₃)

private theorem left_higher_eval_lower :
    -(1650000000000000 : ℝ) ≤ gaussianK131PolyHigher.eval (2 * Real.log (465644807 / 400000)) := by
  have hx := k131_left_log_bounds
  have h :=
    higher_eval_lower (x := 2 * Real.log (465644807 / 400000)) (1412 / 100) (2814 / 100)
      (2374 / 100) 68100000000000000 3230000000000000 (by linarith only [hx.1])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_ofNat] at h
  linarith only [h]

/-- The higher reflection contribution at the left K131 endpoint is bounded
by the rational moment cap and the lower eighth-root enclosure. -/
theorem k131_left_reflect27_lower :
    let y : ℝ := 465644807 / 400000
    (-(4 / 1000000 : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 7) * (gaussianK131GapPoly 7).eval (2 * Real.log y)) := by
  let y : ℝ := 465644807 / 400000
  let r := y ^ (1 / 8 : ℝ)
  let a : ℝ := 24168480494 / 10000000000
  have ha : 0 < a := by
    dsimp only [a]; norm_num only
  have hr : a ≤ r := k131_left_root_bounds.1
  have hi : (r ^ (54 : ℕ))⁻¹ ≤ (a ^ (54 : ℕ))⁻¹ :=
    inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hr _)
  change _ ≤ r ^ (-54 : ℤ) * gaussianK131PolyHigher.eval _
  rw [zpow_neg, zpow_ofNat]
  have h :=
    mul_le_mul_of_nonneg_left left_higher_eval_lower
      (inv_nonneg.mpr (pow_nonneg (ha.le.trans hr) 54))
  have h' := mul_le_mul_of_nonpos_left hi (by norm_num only : -(1650000000000000 : ℝ) ≤ 0)
  dsimp only [a] at h'
  linarith only [h, h']

private theorem right_higher_eval_lower :
    -(73000000000000000 : ℝ) ≤ gaussianK131PolyHigher.eval (2 * Real.log (1036273 / 250)) := by
  have hx := k131_right_log_bounds
  have h :=
    higher_eval_lower (x := 2 * Real.log (1036273 / 250)) (1666 / 100) (3322 / 100) (2882 / 100)
      1940000000000000000 145000000000000000 (by linarith only [hx.1])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; linarith only [hx.2])
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_ofNat] at h
  linarith only [h]

/-- The higher reflection contribution at the right K131 endpoint is bounded
by the rational moment cap and the lower eighth-root enclosure. -/
theorem k131_right_reflect27_lower :
    let y : ℝ := 1036273 / 250
    (-(4 / 100000000 : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 7) * (gaussianK131GapPoly 7).eval (2 * Real.log y)) := by
  let y : ℝ := 1036273 / 250
  let r := y ^ (1 / 8 : ℝ)
  let a : ℝ := 28326425319 / 10000000000
  have ha : 0 < a := by
    dsimp only [a]; norm_num only
  have hr : a ≤ r := k131_right_root_bounds.1
  have hi : (r ^ (54 : ℕ))⁻¹ ≤ (a ^ (54 : ℕ))⁻¹ :=
    inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le hr _)
  change _ ≤ r ^ (-54 : ℤ) * gaussianK131PolyHigher.eval _
  rw [zpow_neg, zpow_ofNat]
  have h :=
    mul_le_mul_of_nonneg_left right_higher_eval_lower
      (inv_nonneg.mpr (pow_nonneg (ha.le.trans hr) 54))
  have h' := mul_le_mul_of_nonpos_left hi (by norm_num only : -(73000000000000000 : ℝ) ≤ 0)
  dsimp only [a] at h'
  linarith only [h, h']

/-- The leading, constant and two main tail terms still needed for the
K131 endpoint comparison after the loss and reflection terms are bounded. -/
noncomputable def k131EndpointFourTerms (y : ℝ) : ℝ :=
  ∑ j ∈ ((((Finset.univ : Finset (Fin 8)).erase 5).erase 2).erase 6).erase 7,
    (y ^ (1 / 8 : ℝ)) ^ (k131GapPower j) * (gaussianK131GapPoly j).eval (2 * Real.log y)

/-- A lower estimate for the four main terms concludes the left endpoint
comparison after all the loss and reflection terms have been included. -/
theorem k131_left_gap_of_four
    (h : (2292734 / 1000000 : ℝ) < k131EndpointFourTerms (465644807 / 400000)) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  apply k131_left_gap_of_five
  have hm : (7 : Fin 8) ∈ ((Finset.univ.erase 5).erase 2).erase 6 := by decide
  rw [← Finset.sum_erase_add _ _ hm]
  unfold k131EndpointFourTerms at h
  linarith only [h, k131_left_reflect27_lower]

/-- A lower estimate for the four main terms concludes the right endpoint
comparison after all the loss and reflection terms have been included. -/
theorem k131_right_gap_of_four
    (h : (332070604 / 100000000 : ℝ) < k131EndpointFourTerms (1036273 / 250)) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  apply k131_right_gap_of_five
  have hm : (7 : Fin 8) ∈ ((Finset.univ.erase 5).erase 2).erase 6 := by decide
  rw [← Finset.sum_erase_add _ _ hm]
  unfold k131EndpointFourTerms at h
  linarith only [h, k131_right_reflect27_lower]

private theorem cast_inverse_moment_rat (a z : ℚ) (m : ℕ) :
    (inverseMomentRat a z m : ℝ) =
      (k131MomentPoly gaussianK131InversePoly (a : ℝ) m).eval (z : ℝ) := by
  simp only [inverseMomentRat, eval_inverse_moment, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_pow]

private def positivePoleRat : ℚ :=
  gaussianK131Amplitude * kernelNumerator (35 / 16) ^ 2 / (35 / 16 : ℚ) ^ 20

private theorem pole_sum_eq :
    (∑ j : Fin 4, gram j * Real.exp (-(offsets j) / 2)) =
      (1831 / 10000 : ℝ) - (973 / 5000 : ℝ) * Real.exp (-(1 / 20)) +
          (1 / 80 : ℝ) * Real.exp (-(21 / 20)) -
        (13 / 1250 : ℝ) * Real.exp (-(9 / 4)) := by
  rw [Fin.sum_univ_four]
  change
    (1831 / 10000 : ℝ) * Real.exp (-0 / 2) + (-973 / 5000) * Real.exp (-(1 / 10) / 2) +
        (1 / 80) * Real.exp (-(21 / 10) / 2) +
        (-13 / 1250) * Real.exp (-(9 / 2) / 2) =
      _
  norm_num only [neg_zero, zero_div, Real.exp_zero, mul_one]
  ring_nf

private theorem alpha_eval_expanded :
    k131Alpha =
      ((4 * gaussianK131Amplitude * inverseMomentRat (35 / 16) (9 / 4) : ℚ) : ℝ) *
          Real.exp ((-243 / 64 : ℚ) : ℝ) -
        (positivePoleRat : ℝ) * Real.exp ((9 / 8 : ℚ) : ℝ) -
        ((3 * positivePoleRat : ℚ) : ℝ) *
          (((1831 / 10000 : ℚ) : ℝ) - ((973 / 5000 : ℚ) : ℝ) * Real.exp ((-1 / 20 : ℚ) : ℝ) +
              ((1 / 80 : ℚ) : ℝ) * Real.exp ((-21 / 20 : ℚ) : ℝ) -
            ((13 / 1250 : ℚ) : ℝ) * Real.exp ((-9 / 4 : ℚ) : ℝ)) := by
  have hm := cast_inverse_moment_rat (35 / 16) (9 / 4) 0
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  rw [k131Alpha, k131Prefactor, ← hm, pole_sum_eq]
  change _ = _
  simp only [positivePole, positivePoleRat, Rat.cast_mul, Rat.cast_neg, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_one]
  ring_nf

private theorem alpha_lower : (0.72086441 : ℝ) ≤ k131Alpha := by
  rw [alpha_eval_expanded]
  dyadic_interval [prec := 66]

private def endpointOffset : Fin 4 → ℚ :=
  ![0, 1 / 10, 21 / 10, 9 / 2]

private def endpointGram : Fin 4 → ℚ :=
  ![1831 / 10000, -973 / 5000, 1 / 80, -13 / 1250]

private theorem endpoint_offset_cast (j : Fin 4) : (endpointOffset j : ℝ) = offsets j := by
  fin_cases j
  · change ((0 : ℚ) : ℝ) = 0
    exact Rat.cast_zero
  · change ((1 / 10 : ℚ) : ℝ) = 1 / 10
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  · change ((21 / 10 : ℚ) : ℝ) = 21 / 10
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  · change ((9 / 2 : ℚ) : ℝ) = 9 / 2
    norm_num only [Rat.cast_div, Rat.cast_ofNat]

private theorem endpoint_gram_cast (j : Fin 4) : (endpointGram j : ℝ) = gram j := by
  fin_cases j
  · change ((1831 / 10000 : ℚ) : ℝ) = 1831 / 10000
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  · change ((-973 / 5000 : ℚ) : ℝ) = -973 / 5000
    norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
  · change ((1 / 80 : ℚ) : ℝ) = 1 / 80
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  · change ((-13 / 1250 : ℚ) : ℝ) = -13 / 1250
    norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]

private def fourierEvalRat (z : ℚ) : ℚ :=
  gaussianK131Amplitude * ∑ j : Fin 9, ∑ k ∈ Finset.range (10 - j.val), fourierTerm j k * z ^ k

private theorem cast_fourier_eval (z : ℚ) :
    (fourierEvalRat z : ℝ) = gaussianK131Fourier.eval (z : ℝ) := by
  simp only [fourierEvalRat, gaussianK131Fourier, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow]

private theorem conductor_expanded :
    shiftedConductor =
      (∑ j : Fin 4,
          let h : ℚ := 9 / 4 + endpointOffset j
          ((2 * endpointGram j * fourierEvalRat |h| : ℚ) : ℝ) *
            Real.exp ((-(27 / 16) * |h| : ℚ) : ℝ)) -
        ∑ i : Fin 4,
          ∑ j : Fin 4,
            let h := endpointOffset i - endpointOffset j
            ((endpointGram i * endpointGram j * fourierEvalRat |h| : ℚ) : ℝ) *
              Real.exp ((-(27 / 16) * |h| : ℚ) : ℝ) := by
  unfold shiftedConductor
  have h (z : ℚ) :
    fourierMass (z : ℝ) = 2 * Real.exp ((-(27 / 16) * |z| : ℚ) : ℝ) * (fourierEvalRat |z| : ℝ) := by
    simp only [fourierMass, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_abs,
      cast_fourier_eval]
  have he : (9 / 4 : ℝ) = ((9 / 4 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  simp only [← endpoint_gram_cast, ← endpoint_offset_cast, he, ← Rat.cast_add, ← Rat.cast_sub, h,
    Rat.cast_mul, Rat.cast_ofNat]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem beta_upper : k131Beta ≤ 0.74946597 := by
  rw [k131Beta, conductor_expanded]
  simp only [Fin.sum_univ_four]
  have h : (3 / 4 : ℝ) = 0.75 := by norm_num only
  rw [h]
  dyadic_interval [prec := 66]

private theorem endpoint_leading_lower {y : ℝ} (hy : 0 ≤ y) :
    y * (0.72086441 - 0.74946597 / (2 * (519674 / 1000000))) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 0) * (gaussianK131GapPoly 0).eval (2 * Real.log y) := by
  change
    _ ≤
      (y ^ (1 / 8 : ℝ)) ^ (8 : ℤ) *
        (Polynomial.C (k131Alpha - k131Beta / (2 * (519674 / 1000000)))).eval _
  rw [Polynomial.eval_C, ← k131_rpow_eighth hy]
  have he : ((8 : ℤ) : ℝ) / 8 = 1 := by norm_num only
  rw [he, Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hy
  exact sub_le_sub alpha_lower (div_le_div_of_nonneg_right beta_upper (by norm_num only))

/-- Lower bound on the leading contribution at the left K131 endpoint. -/
theorem k131_left_leading_lower :
    let y : ℝ := 465644807 / 400000
    (-(0.26544 : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 0) * (gaussianK131GapPoly 0).eval (2 * Real.log y)) := by
  refine le_trans ?_ (endpoint_leading_lower (by norm_num only))
  norm_num only

/-- Lower bound on the leading contribution at the right K131 endpoint. -/
theorem k131_right_leading_lower :
    let y : ℝ := 1036273 / 250
    (-(0.94515 : ℝ) ≤
      (y ^ (1 / 8 : ℝ)) ^ (k131GapPower 0) * (gaussianK131GapPoly 0).eval (2 * Real.log y)) := by
  refine le_trans ?_ (endpoint_leading_lower (by norm_num only))
  norm_num only

/-- Constant and main tail contributions after removing the leading term. -/
noncomputable def k131EndpointMainTerms (y : ℝ) : ℝ :=
  ∑ j ∈ (((((Finset.univ : Finset (Fin 8)).erase 5).erase 2).erase 6).erase 7).erase 0,
    (y ^ (1 / 8 : ℝ)) ^ (k131GapPower j) * (gaussianK131GapPoly j).eval (2 * Real.log y)

/-- Three main term bounds now suffice for the left endpoint. -/
theorem k131_left_gap_of_main_terms
    (h : (2.558174 : ℝ) < k131EndpointMainTerms (465644807 / 400000)) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  apply k131_left_gap_of_four
  unfold k131EndpointFourTerms
  have hm : (0 : Fin 8) ∈ (((Finset.univ.erase 5).erase 2).erase 6).erase 7 := by decide
  rw [← Finset.sum_erase_add _ _ hm]
  unfold k131EndpointMainTerms at h
  linarith only [h, k131_left_leading_lower]

/-- Three main term bounds now suffice for the right endpoint. -/
theorem k131_right_gap_of_main_terms
    (h : (4.26585604 : ℝ) < k131EndpointMainTerms (1036273 / 250)) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  apply k131_right_gap_of_four
  unfold k131EndpointFourTerms
  have hm : (0 : Fin 8) ∈ (((Finset.univ.erase 5).erase 2).erase 6).erase 7 := by decide
  rw [← Finset.sum_erase_add _ _ hm]
  unfold k131EndpointMainTerms at h
  linarith only [h, k131_right_leading_lower]

private def halfLineRat : ℚ :=
  gaussianK131Amplitude * kernelNumerator (19 / 16) * kernelNumerator (35 / 16) /
    ((27 / 16 : ℚ) ^ 2 - 1 / 4) ^ 10

private noncomputable def endpointCosh (t : ℚ) : ℝ :=
  (0.5 : ℝ) * (Real.exp (t : ℝ) + Real.exp ((-t : ℚ) : ℝ))

private theorem endpoint_cosh_eq (t : ℚ) : Real.cosh (t : ℝ) = endpointCosh t := by
  rw [Real.cosh_eq, endpointCosh, Rat.cast_neg]
  ring

private theorem reflected_expanded :
    reflectedConstant =
      (∑ j : Fin 4,
            ((-6 * halfLineRat * endpointGram j : ℚ) : ℝ) *
              endpointCosh ((9 / 4 + endpointOffset j) / 2)) +
          (∑ i : Fin 4,
            ∑ j : Fin 4,
              ((3 * halfLineRat * endpointGram i * endpointGram j : ℚ) : ℝ) *
                endpointCosh ((endpointOffset i - endpointOffset j) / 2)) -
        ((3 * (2 * (∑ j : Fin 4, |endpointGram j|) + (∑ j : Fin 4, |endpointGram j|) ^ 2 / 2) /
              100000 :
            ℚ) :
          ℝ) := by
  have hhalf : halfLineMass = (halfLineRat : ℝ) := rfl
  have he : (9 / 4 : ℝ) = ((9 / 4 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  unfold reflectedConstant gramAbsMass
  simp only [hhalf, ← endpoint_gram_cast, ← endpoint_offset_cast, he, ← Rat.cast_abs,
    ← Rat.cast_sub, ← Rat.cast_add, ← Rat.cast_sum]
  have hcos (t : ℚ) : Real.cosh ((t : ℝ) / 2) = endpointCosh (t / 2) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using endpoint_cosh_eq (t / 2)
  simp only [hcos, Finset.mul_sum, Rat.cast_mul, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_div,
    Rat.cast_add, Rat.cast_pow]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have h' :
        Real.cosh ((9 / 4 + (endpointOffset j : ℝ)) / 2) =
          endpointCosh ((9 / 4 + endpointOffset j) / 2) := by
        simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using
          hcos (9 / 4 + endpointOffset j)
      rw [h']
      ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  · ring_nf
    rw [← Finset.sum_mul, Rat.cast_mul]
    norm_num only [Rat.cast_ofNat]
    ring

private theorem reflected_lower : (2.04623332 : ℝ) ≤ reflectedConstant := by
  rw [reflected_expanded]
  simp only [Fin.sum_univ_four, endpointCosh]
  dyadic_interval [prec := 66]

private def momentAt (a z : ℚ) : ℚ :=
  ∑ j : Fin 9, inverseCoeffs j * tailRat a (2 * j.val + 3) z

private theorem moment_expanded {a : ℚ} (ha : 0 < a) :
    gaussianK131Moment (a : ℝ) =
      (momentAt a 0 : ℝ) - Real.exp ((-a * (9 / 4) : ℚ) : ℝ) * (momentAt a (9 / 4) : ℝ) := by
  rw [k131_moment_eval _ ((Rat.cast_pos (K := ℝ)).mpr ha)]
  simp only [momentAt, Rat.cast_sum, Rat.cast_mul, cast_tail_rat, Rat.cast_neg, Rat.cast_zero,
    Rat.cast_div, Rat.cast_ofNat, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  apply congrArg₂ Sub.sub rfl
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem constant_moment_lower : (0.42491945 : ℝ) ≤ gaussianK131Moment (27 / 16) := by
  have hm := moment_expanded (a := 27 / 16) (by decide +kernel)
  have he : (27 / 16 : ℝ) = ((27 / 16 : ℚ) : ℝ) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [he, hm]
  dyadic_interval [prec := 66]

private theorem constant_term_lower (x : ℝ) : (9.04129 : ℝ) ≤ (gaussianK131GapPoly 1).eval x := by
  have hh : (2.62804849 : ℝ) ≤ halfLineMass := by
    change _ ≤ (halfLineRat : ℝ)
    dyadic_interval [prec := 66]
  have ha : (0.14305492 : ℝ) ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hm :=
    mul_le_mul ha constant_moment_lower (by norm_num only)
      ((by norm_num only : (0 : ℝ) ≤ 0.14305492).trans ha)
  change
    _ ≤
      (Polynomial.C
            (6 * halfLineMass - 3 / 100000 - 25329 / 1000000 + reflectedConstant -
                k131Beta * (123 / 10) / (2 * (519674 / 1000000)) +
              2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16))).eval
        x
  rw [Polynomial.eval_C]
  have hb :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right beta_upper (by norm_num only : (0 : ℝ) ≤ 123 / 10))
      (by norm_num only : (0 : ℝ) ≤ 2 * (519674 / 1000000))
  norm_num only at hb hm
  norm_num only
  linarith only [hh, reflected_lower, hb, hm]

/-- The two main tail terms that remain in the K131 endpoint comparison. -/
noncomputable def k131EndpointTailTerms (y : ℝ) : ℝ :=
  let r := y ^ (1 / 8 : ℝ)
  let x := 2 * Real.log y
  r ^ (-19 : ℤ) * gaussianK131Poly19.eval x + r ^ (-27 : ℤ) * gaussianK131Poly27.eval x

private theorem endpoint_main_split (y : ℝ) :
    k131EndpointMainTerms y =
      (gaussianK131GapPoly 1).eval (2 * Real.log y) + k131EndpointTailTerms y := by
  unfold k131EndpointMainTerms
  have hs :
    (((((Finset.univ : Finset (Fin 8)).erase 5).erase 2).erase 6).erase 7).erase 0 = {1, 3, 4} := by
    decide +kernel
  rw [hs, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  change _ ^ (0 : ℤ) * _ + (_ + _) = _
  rw [zpow_zero, one_mul]
  rfl

/-- The left endpoint inequality follows once the two tail terms
together are greater than -6.483116. -/
theorem k131_left_gap_of_tail_terms
    (h : -(6.483116 : ℝ) < k131EndpointTailTerms (465644807 / 400000)) :
    (1 / 200 : ℝ) < gaussianK131Gap (465644807 / 400000) := by
  apply k131_left_gap_of_main_terms
  rw [endpoint_main_split]
  linarith only [h, constant_term_lower (2 * Real.log (465644807 / 400000))]

/-- The right endpoint inequality follows once the two tail terms
together are greater than -4.77543396. -/
theorem k131_right_gap_of_tail_terms
    (h : -(4.77543396 : ℝ) < k131EndpointTailTerms (1036273 / 250)) :
    (1 / 200 : ℝ) < gaussianK131Gap (1036273 / 250) := by
  apply k131_right_gap_of_main_terms
  rw [endpoint_main_split]
  linarith only [h, constant_term_lower (2 * Real.log (1036273 / 250))]

end PseudoPrime.PrimeTestBounds.MillerRabin
