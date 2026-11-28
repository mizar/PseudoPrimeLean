/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSpectralBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSpectralBudget
import Mathlib.Tactic

/-! # Exponential integrals for the shared six-pole Gaussian kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem six_pole_anti_eval (s z : ℂ) :
    (k131AntiPoly (Polynomial.X ^ 5) s).eval z =
      z ^ 5 / s + 5 * z ^ 4 / s ^ 2 + 20 * z ^ 3 / s ^ 3 + 60 * z ^ 2 / s ^ 4 + 120 * z / s ^ 5 +
        120 / s ^ 6 := by
  simp only [k131AntiPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← Finset.sum_subset (Finset.range_mono (show 6 ≤ 20 from by decide))]
  · norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.descFactorial, Nat.cast_ofNat,
      Nat.cast_one, Nat.reduceSub, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one, zero_add]
    simp only [div_eq_mul_inv]
    ring
  · intro j _ hj
    have hj' := Nat.le_of_not_lt (fun h ↦ hj (Finset.mem_range.mpr h))
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_succ_le hj'), Nat.cast_zero, zero_mul,
      mul_zero]

/-- The polynomial part of the exponential antiderivative for a fifth-power kernel. -/
public noncomputable def gaussianSixPoleAnti (s z : ℂ) : ℂ :=
  z ^ 5 / s + 5 * z ^ 4 / s ^ 2 + 20 * z ^ 3 / s ^ 3 + 60 * z ^ 2 / s ^ 4 + 120 * z / s ^ 5 +
    120 / s ^ 6

/-- Evaluate the real part of the six-pole integral between arbitrary real endpoints. -/
public theorem gaussian_six_pole_integral {s : ℂ} (hs : s ≠ 0) (c : ℂ) (a b : ℝ) :
    (∫ t in a..b, (c * Complex.exp (-s * (t : ℂ)) * (t : ℂ) ^ 5).re) =
      (c * Complex.exp (-s * (a : ℂ)) * gaussianSixPoleAnti s (a : ℂ) -
          c * Complex.exp (-s * (b : ℂ)) * gaussianSixPoleAnti s (b : ℂ)).re := by
  have hP : (Polynomial.X ^ 5 : Polynomial ℂ).natDegree < 20 := by
    rw [Polynomial.natDegree_X_pow]
    decide
  simpa only [Polynomial.eval_pow, Polynomial.eval_X, six_pole_anti_eval, gaussianSixPoleAnti] using
    k131_complex_exp_integral hP hs c a b

/-- The lower cutoff moment is the six-pole antiderivative at the fixed window width. -/
public theorem gaussian_spectral_moment_eq (γ : ℝ) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    gaussianSpectralMoment γ =
      (C : ℂ) * gaussianSixPoleAnti ((a : ℂ) + (γ : ℂ) * Complex.I) (b : ℂ) := by
  intro a b C
  unfold gaussianSpectralMoment gaussianSixPoleAnti
  change (C : ℂ) * _ = (C : ℂ) * _
  congr 1
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, kernelMomentCoeff, b, Complex.ofReal_div,
    Complex.ofReal_ofNat, Rat.cast_div, Rat.cast_ofNat, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    pow_one, add_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-- Split the signed pair of integrals at the common cutoff. The endpoint at
the physical lower limit is retained explicitly for subsequent error bounds. -/
public theorem gaussian_six_pole_signed_integrals {s : ℂ} (hs : s ≠ 0) (c : ℂ) (b z : ℝ) :
    let g := fun v : ℝ ↦ (c * Complex.exp (-s * (v : ℂ)) * (v : ℂ) ^ 5).re
    let F := fun v : ℝ ↦ (c * Complex.exp (-s * (v : ℂ)) * gaussianSixPoleAnti s (v : ℂ)).re
    3 * (∫ v in b..z, g v) - (∫ v in (0 : ℝ)..b, g v) = 4 * F b - F 0 - 3 * F z := by
  intro g F
  have h (l r : ℝ) : (∫ v in l..r, g v) = F l - F r := by
    simpa only [Complex.sub_re] using gaussian_six_pole_integral hs c l r
  rw [h, h]
  ring

/-- Normalize the common cutoff coefficient and isolate the physical lower
endpoint. The phase can include any scalar, including zero multiplicity. -/
public theorem gaussian_six_pole_spectral_split {γ : ℝ} (hγ : γ ≠ 0) (p : ℂ) (z : ℝ) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
    let s := (a : ℂ) + (γ : ℂ) * Complex.I
    let F := fun v : ℝ ↦
      p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (v : ℂ))) * gaussianSixPoleAnti s (v : ℂ)
    p * (4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ) - 4 * F b + F 0 + 3 * F z =
      p * gaussianSpectralCoeff γ + 3 * F z := by
  intro a b C ρ s F
  have hb : F b = p * gaussianSpectralMoment γ := by
    rw [gaussian_spectral_moment_eq]
    dsimp only [F]
    rw [sub_self, mul_zero, Complex.exp_zero, mul_one, mul_assoc]
  have he :
    Complex.exp (s * (b : ℂ)) =
      (Real.exp (a * b) : ℂ) * Complex.exp (((b * γ : ℝ) : ℂ) * Complex.I) := by
    rw [show s * (b : ℂ) = ((a * b : ℝ) : ℂ) + (((b * γ : ℝ) : ℂ) * Complex.I)
        by
        simp only [s, Complex.ofReal_mul]
        ring,
      Complex.exp_add, Complex.ofReal_exp]
  have hc : (C : ℂ) * (Real.exp (a * b) : ℂ) = ((a ^ 5 : ℝ) : ℂ) / 120 := by
    rw [← Complex.ofReal_mul]
    change ((a ^ 5 * Real.exp (-(a * b)) / 120 * Real.exp (a * b) : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, div_mul_eq_mul_div, ←
      Complex.ofReal_mul, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have h0 :
    F 0 = p * (((a ^ 5 : ℝ) : ℂ) * Complex.exp (((b * γ : ℝ) : ℂ) * Complex.I) / s ^ 6) := by
    dsimp only [F, gaussianSixPoleAnti]
    simp only [Complex.ofReal_zero, sub_zero, zero_pow (by decide : 5 ≠ 0),
      zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_div, zero_add, he]
    rw [mul_assoc p, ← mul_assoc (C : ℂ), hc]
    ring
  rw [hb, h0, gaussian_spectral_coeff_eq hγ]
  ring

/-- Evaluate the signed coordinate integral and its cutoff term using the
certified spectral coefficient and the one remaining endpoint. -/
public theorem gaussian_six_pole_spectral_integral {γ : ℝ} (hγ : γ ≠ 0) (p : ℂ) (z : ℝ) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
    let s := (a : ℂ) + (γ : ℂ) * Complex.I
    let g := fun v : ℝ ↦ (p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (v : ℂ))) * (v : ℂ) ^ 5).re
    (p * (4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ)).re - 3 * (∫ v in b..z, g v) + (∫ v in (0 : ℝ)..b, g v) =
      (p * gaussianSpectralCoeff γ).re +
        3 *
          (p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (z : ℂ))) *
              gaussianSixPoleAnti s (z : ℂ)).re := by
  intro a b C ρ s g
  have hs : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num only [s, a, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hr
  have he (v : ℝ) :
    p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (v : ℂ))) =
      p * (C : ℂ) * Complex.exp (s * (b : ℂ)) * Complex.exp (-s * (v : ℂ)) := by
    rw [mul_sub, sub_eq_add_neg, ← neg_mul, Complex.exp_add, ← mul_assoc]
  have hi := gaussian_six_pole_signed_integrals hs (p * (C : ℂ) * Complex.exp (s * (b : ℂ))) b z
  dsimp only at hi
  simp only [← he] at hi
  change 3 * (∫ v in b..z, g v) - (∫ v in (0 : ℝ)..b, g v) = _ at hi
  have hc := congrArg Complex.re (gaussian_six_pole_spectral_split hγ p z)
  dsimp only at hc
  have h3 (w : ℂ) : (3 * w).re = 3 * w.re := by
    change ((((3 : ℝ) : ℂ) * w).re) = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h4 (w : ℂ) : (4 * w).re = 4 * w.re := by
    change ((((4 : ℝ) : ℂ) * w).re) = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.add_re, Complex.sub_re, h3, h4] at hc
  dsimp only [a, b, C, ρ, s] at hi ⊢
  linarith only [hi, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
