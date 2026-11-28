/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelSquare
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # The compact coordinate of the high Gaussian square kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reciprocal of the shifted line point, parameterized by height. -/
@[expose]
public noncomputable def highPoleInv (a t : ℝ) : ℂ :=
  ((a : ℂ) + Complex.I * t)⁻¹

/-- The compact coordinate on the shifted vertical line. -/
@[expose]
public noncomputable def highCompactCoord (a t : ℝ) : ℂ :=
  1 - (2 * (a : ℂ)) * highPoleInv a t

private theorem high_pole_ne {a : ℝ} (ha : 0 < a) (t : ℝ) : (a : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.zero_re, zero_mul, mul_zero, sub_zero, add_zero] at he
  exact ha.ne' he

/-- The reciprocal pole derivative is the negative imaginary unit times its square. -/
public theorem high_pole_inv_deriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (highPoleInv a) (-Complex.I * highPoleInv a t ^ 2) t := by
  have h :=
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).const_mul
          Complex.I).const_add
      (a : ℂ)
  have hd : HasDerivAt (fun u : ℝ ↦ (a : ℂ) + Complex.I * u) Complex.I t := by
    simpa only [Function.comp_apply, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one,
      mul_one] using h
  refine (hd.inv (high_pole_ne ha t)).congr_deriv ?_
  simp only [highPoleInv, inv_pow, div_eq_mul_inv]

/-- The compact coordinate derivative has the two-pole decay used in H26. -/
public theorem high_compact_coord_deriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (highCompactCoord a) (2 * (a : ℂ) * Complex.I * highPoleInv a t ^ 2) t := by
  have h := (hasDerivAt_const t (1 : ℂ)).sub ((high_pole_inv_deriv ha t).const_mul (2 * (a : ℂ)))
  refine h.congr_deriv ?_
  ring

/-- The compact coordinate has unit norm on the vertical line. -/
public theorem high_compact_coord_norm {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖highCompactCoord a t‖ = 1 := by
  have h : highCompactCoord a t = (-(a : ℂ) + Complex.I * t) / ((a : ℂ) + Complex.I * t) := by
    unfold highCompactCoord highPoleInv
    field_simp [high_pole_ne ha t]
    ring
  rw [h, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (high_pole_ne ha t))]
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add, one_mul]
  ring

/-- The imaginary part controls the norm of the shifted pole. -/
private theorem high_pole_inv_norm {a t : ℝ} (ht : 0 < t) : ‖highPoleInv a t‖ ≤ 1 / t := by
  have hi := Complex.abs_im_le_norm ((a : ℂ) + Complex.I * t)
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add, abs_of_pos ht] at hi
  rw [highPoleInv, norm_inv, ← one_div]
  exact one_div_le_one_div_of_le ht hi

/-- Compact polynomial times the square of the reciprocal pole. -/
@[expose]
public noncomputable def highCompactQuot (P : Polynomial ℂ) (a t : ℝ) : ℂ :=
  highPoleInv a t ^ 2 * P.eval (highCompactCoord a t)

/-- Differentiate the compact quotient by the product and chain rules. -/
public theorem high_compact_quot_deriv (P : Polynomial ℂ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (highCompactQuot P a)
      ((2 : ℂ) * highPoleInv a t * (-Complex.I * highPoleInv a t ^ 2) *
          P.eval (highCompactCoord a t) +
        highPoleInv a t ^ 2 *
          (P.derivative.eval (highCompactCoord a t) *
            (2 * (a : ℂ) * Complex.I * highPoleInv a t ^ 2)))
      t := by
  have h :=
    ((high_pole_inv_deriv ha t).pow 2).mul
      ((P.hasDerivAt (highCompactCoord a t)).comp t (high_compact_coord_deriv ha t))
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]

/-- Bounds on the compact polynomial and its derivative on the unit circle give
the quotient estimates in H26. -/
public theorem high_compact_quot_bounds (P : Polynomial ℂ) {a t M₀ M₁ : ℝ} (ha : 0 < a) (ht : 0 < t)
    (h₀ : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ M₀) (h₁ : ∀ z : ℂ, ‖z‖ = 1 → ‖P.derivative.eval z‖ ≤ M₁) :
    ‖highCompactQuot P a t‖ ≤ M₀ / t ^ 2 ∧
      ‖deriv (highCompactQuot P a) t‖ ≤ 2 * M₀ / t ^ 3 + 2 * a * M₁ / t ^ 4 := by
  let u := highPoleInv a t
  let z := highCompactCoord a t
  have hu := high_pole_inv_norm (a := a) ht
  have hz := high_compact_coord_norm ha t
  have hP := h₀ z hz
  have hP' := h₁ z hz
  have hM₁ := (norm_nonneg _).trans hP'
  have hu₂ := pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hf := mul_le_mul hu₂ hP (norm_nonneg _) (sq_nonneg _)
  constructor
  · rw [highCompactQuot, norm_mul, norm_pow]
    exact hf.trans_eq (by ring)
  rw [(high_compact_quot_deriv P ha t).deriv]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ha, one_mul, mul_one, norm_pow]
  change 2 * ‖u‖ * ‖u‖ ^ 2 * ‖P.eval z‖ + ‖u‖ ^ 2 * (‖P.derivative.eval z‖ * (2 * a * ‖u‖ ^ 2)) ≤ _
  have hA :=
    mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num only : (0 : ℝ) ≤ 2)) hu₂ (sq_nonneg _)
        (mul_nonneg (by norm_num only) (one_div_nonneg.mpr ht.le)))
      hP (norm_nonneg _) (by positivity)
  have hcoef : 0 ≤ 2 * a := mul_nonneg (by norm_num only) ha.le
  have hprod :=
    mul_le_mul hP' (mul_le_mul_of_nonneg_left hu₂ hcoef) (mul_nonneg hcoef (sq_nonneg ‖u‖)) hM₁
  have hB :=
    mul_le_mul hu₂ hprod
      (mul_nonneg (norm_nonneg (P.derivative.eval z)) (mul_nonneg hcoef (sq_nonneg ‖u‖)))
      (sq_nonneg (1 / t))
  exact (add_le_add hA hB).trans_eq (by ring)

/-- Real normalized coefficient of the compact polynomial in its disk coordinate. -/
public noncomputable def highCompactWeight (K : HighGaussianKernel) (j : ℕ) : ℝ :=
  (((coefficientTicks K)[j]?.getD 0 : ℤ) : ℝ) / ((coefficientTicks K).sum : ℝ)

/-- The polynomial in the unit-modulus coordinate of the compact numerator. -/
@[expose]
public noncomputable def highCompactPoly (K : HighGaussianKernel) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (K.degree + 1), Polynomial.monomial j (Complex.ofReal (highCompactWeight K j))

/-- The absolute coefficient sum appearing in the manuscript's bound for the compact quotient. -/
@[expose]
public noncomputable def highCompactMass (K : HighGaussianKernel) : ℝ :=
  ∑ j ∈ Finset.range (K.degree + 1), |highCompactWeight K j|

/-- The absolute coefficient sum weighted by degree bounds the compact derivative. -/
@[expose]
public noncomputable def highCompactSlope (K : HighGaussianKernel) : ℝ :=
  ∑ j ∈ Finset.range (K.degree + 1), (j : ℝ) * |highCompactWeight K j|

/-- The compact polynomial and its derivative are bounded by their coefficient sums. -/
public theorem high_compact_poly_bounds (K : HighGaussianKernel) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(highCompactPoly K).eval z‖ ≤ highCompactMass K ∧
      ‖(highCompactPoly K).derivative.eval z‖ ≤ highCompactSlope K := by
  constructor
  · simp only [highCompactPoly, highCompactMass, Polynomial.eval_finsetSum,
      Polynomial.eval_monomial]
    refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun j _ ↦ ?_))
    rw [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · simp only [highCompactPoly, highCompactSlope, Polynomial.derivative_sum,
      Polynomial.derivative_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun j _ ↦ ?_))
    simp only [norm_mul, norm_pow, hz, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast, mul_comm]

/-- The H26 quotient bounds for the actual K186 and K196 coefficient sums. -/
public theorem high_kernel_quot_bounds (K : HighGaussianKernel) {t : ℝ} (ht : 0 < t) :
    let a := (K.pole : ℝ)
    ‖highCompactQuot (highCompactPoly K) a t‖ ≤ highCompactMass K / t ^ 2 ∧
      ‖deriv (highCompactQuot (highCompactPoly K) a) t‖ ≤
        2 * highCompactMass K / t ^ 3 + 2 * a * highCompactSlope K / t ^ 4 := by
  exact
    high_compact_quot_bounds _
      ((by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)) ht
      (fun _ hz ↦ (high_compact_poly_bounds K hz).1) (fun _ hz ↦ (high_compact_poly_bounds K hz).2)

/-- On the vertical line the compact quotient matches the original squared-kernel numerator
divided by two more powers than its compact degree. -/
public theorem high_compact_quot_eq (K : HighGaussianKernel) (t : ℝ) :
    let a := (K.pole : ℝ)
    let w := (a : ℂ) + Complex.I * t
    highCompactQuot (highCompactPoly K) a t =
      K.polynomial.eval₂ (Rat.castHom ℂ) w / w ^ (K.degree + 2) := by
  intro a w
  have ha : 0 < a := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hw : w ≠ 0 := high_pole_ne ha t
  have hc : (a : ℂ) = (K.pole : ℂ) := Complex.ofReal_ratCast _
  have hcoord : highCompactCoord a t = (w - 2 * (a : ℂ)) / w := by
    change 1 - (2 * (a : ℂ)) * w⁻¹ = _
    field_simp [hw]
  simp only [highCompactQuot, highCompactPoly, HighGaussianKernel.polynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Rat.coe_castHom, highPoleInv, hcoord, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj ↦ ?_)
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hcast :
    (highCompactWeight K j : ℂ) =
      ((((coefficientTicks K)[j]?.getD 0 : ℤ) : ℚ) / ((coefficientTicks K).sum : ℚ) : ℚ) := by
    simp only [highCompactWeight, Complex.ofReal_div, Complex.ofReal_intCast, Rat.cast_div,
      Rat.cast_intCast]
  have hd : K.degree + 2 = (K.degree - j) + j + 2 := by rw [Nat.sub_add_cancel hj']
  rw [hcast, div_pow, hd, pow_add w ((K.degree - j) + j) 2, pow_add w (K.degree - j) j]
  simp only [Rat.cast_mul, Rat.cast_ofNat, hc]
  change w⁻¹ ^ 2 * _ = _
  field_simp [hw]

/-- The high square kernel on the critical line, in its compact-quotient form. -/
@[expose]
public noncomputable def highHeightKernel (K : HighGaussianKernel) (t : ℝ) : ℂ :=
  (K.normalization : ℂ) * Complex.exp (5 * Complex.I * t) *
    highCompactQuot (highCompactPoly K) K.pole t ^ 2

/-- The compact square equals the original high square kernel. -/
public theorem high_height_kernel_eq (K : HighGaussianKernel) (t : ℝ) :
    let w := (K.pole : ℂ) + Complex.I * t
    highHeightKernel K t =
      (K.normalization : ℂ) * Complex.exp (5 * Complex.I * t) *
          (K.polynomial.eval₂ (Rat.castHom ℂ) w) ^ 2 /
        w ^ (2 * K.degree + 4) := by
  intro w
  have h := high_compact_quot_eq K t
  simp only [Complex.ofReal_ratCast] at h
  rw [highHeightKernel, h, div_pow, ← pow_mul, ← mul_div_assoc]
  congr 2
  ring

/-- The derivative of the modulation factor along the vertical line. -/
private theorem height_phase_deriv (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Complex.exp (5 * Complex.I * x))
      (Complex.exp (5 * Complex.I * t) * (5 * Complex.I)) t := by
  have h :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).const_mul (5 * Complex.I)
  simpa only [Function.comp_apply, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one,
    mul_one] using h.cexp

/-- The compact product estimates yield the square-kernel term of H26. -/
public theorem high_height_kernel_deriv_bound (K : HighGaussianKernel) {t : ℝ} (ht : 0 < t) :
    let a := (K.pole : ℝ)
    let M₀ := highCompactMass K
    let M₁ := highCompactSlope K
    ‖deriv (highHeightKernel K) t‖ ≤
      (K.normalization : ℝ) *
        (5 * M₀ ^ 2 / t ^ 4 + 4 * M₀ ^ 2 / t ^ 5 + 4 * a * M₀ * M₁ / t ^ 6) := by
  intro a M₀ M₁
  let Q := highCompactQuot (highCompactPoly K) a
  have ha : 0 < a := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hκ : 0 < (K.normalization : ℝ) := Rat.cast_pos.mpr (high_gaussian_normalization_pos K)
  have hphase : ‖Complex.exp (5 * Complex.I * (t : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero,
      sub_self, Real.exp_zero]
  have hQ := high_kernel_quot_bounds K ht
  have hD :=
    ((height_phase_deriv t).mul
          ((high_compact_quot_deriv (highCompactPoly K) ha t).pow 2)).const_mul
      (K.normalization : ℂ)
  have he :
    highHeightKernel K = fun x : ℝ ↦
      (K.normalization : ℂ) * (((fun v : ℝ ↦ Complex.exp (5 * Complex.I * v)) * Q ^ 2) x) := by
    funext x
    simp only [highHeightKernel, Q, a, Pi.mul_apply, Pi.pow_apply, mul_assoc]
  rw [he, hD.deriv, norm_mul]
  simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  have hn : ‖(K.normalization : ℂ)‖ = (K.normalization : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ hκ.le
  apply (norm_add_le _ _).trans
  simp only [norm_mul, norm_pow, hphase, Complex.norm_I, Complex.norm_ofNat, mul_one, one_mul]
  rw [← (high_compact_quot_deriv (highCompactPoly K) ha t).deriv]
  change 5 * ‖Q t‖ ^ 2 + 2 * ‖Q t‖ * ‖deriv Q t‖ ≤ _
  have hf := pow_le_pow_left₀ (norm_nonneg (Q t)) hQ.1 2
  have hmul :=
    mul_le_mul (mul_le_mul_of_nonneg_left hQ.1 (by norm_num only : (0 : ℝ) ≤ 2)) hQ.2
      (norm_nonneg _) (mul_nonneg (by norm_num only) ((norm_nonneg (Q t)).trans hQ.1))
  exact (add_le_add (mul_le_mul_of_nonneg_left hf (by norm_num only)) hmul).trans_eq (by ring)

/-- The compact square kernel is differentiable at every real height. -/
public theorem high_height_kernel_differentiable (K : HighGaussianKernel) (t : ℝ) :
    DifferentiableAt ℝ (highHeightKernel K) t := by
  have ha : 0 < (K.pole : ℝ) := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have h := (height_phase_deriv t).differentiableAt
  have hQ := (high_compact_quot_deriv (highCompactPoly K) ha t).differentiableAt
  have hc := (hasDerivAt_const t (K.normalization : ℂ)).differentiableAt
  exact (hc.mul h).mul (hQ.pow 2)

/-- Rational coefficients for the two finite absolute coefficient sums. -/
private def compactWeightRat (K : HighGaussianKernel) (j : ℕ) : ℚ :=
  (((coefficientTicks K)[j]?.getD 0 : ℤ) : ℚ) / ((coefficientTicks K).sum : ℚ)

/-- The rational coefficient casts to the real coefficient used in the norm bound. -/
private theorem compact_weight_cast (K : HighGaussianKernel) (j : ℕ) :
    ((compactWeightRat K j : ℚ) : ℝ) = highCompactWeight K j := by
  simp only [compactWeightRat, highCompactWeight, Rat.cast_div, Rat.cast_intCast]

/-- K186's two absolute coefficient sums are exact rationals. -/
public theorem k186_compact_sums :
    highCompactMass .k186 = 335554205356312 / 813989428426 ∧
      highCompactSlope .k186 = 1729460019748684 / 813989428426 := by
  have h₀ :
    (∑ j ∈ Finset.range (HighGaussianKernel.k186.degree + 1), |compactWeightRat .k186 j|) =
      (335554205356312 / 813989428426 : ℚ) := by
    decide +kernel
  have h₁ :
    (∑ j ∈ Finset.range (HighGaussianKernel.k186.degree + 1),
        (j : ℚ) * |compactWeightRat .k186 j|) =
      (1729460019748684 / 813989428426 : ℚ) := by
    decide +kernel
  exact
    ⟨by
      simpa only [highCompactMass, Rat.cast_sum, Rat.cast_abs, compact_weight_cast, Rat.cast_div,
        Rat.cast_ofNat] using congrArg (fun q : ℚ ↦ (q : ℝ)) h₀,
      by
      simpa only [highCompactSlope, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs,
        compact_weight_cast, Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ ↦ (q : ℝ)) h₁⟩

/-- K196's two absolute coefficient sums are exact rationals. -/
public theorem k196_compact_sums :
    highCompactMass .k196 = 892039868556197 / 970498903459 ∧
      highCompactSlope .k196 = 5454878552018281 / 970498903459 := by
  have h₀ :
    (∑ j ∈ Finset.range (HighGaussianKernel.k196.degree + 1), |compactWeightRat .k196 j|) =
      (892039868556197 / 970498903459 : ℚ) := by
    decide +kernel
  have h₁ :
    (∑ j ∈ Finset.range (HighGaussianKernel.k196.degree + 1),
        (j : ℚ) * |compactWeightRat .k196 j|) =
      (5454878552018281 / 970498903459 : ℚ) := by
    decide +kernel
  exact
    ⟨by
      simpa only [highCompactMass, Rat.cast_sum, Rat.cast_abs, compact_weight_cast, Rat.cast_div,
        Rat.cast_ofNat] using congrArg (fun q : ℚ ↦ (q : ℝ)) h₀,
      by
      simpa only [highCompactSlope, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs,
        compact_weight_cast, Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ ↦ (q : ℝ)) h₁⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
