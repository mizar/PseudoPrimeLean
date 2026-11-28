/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleAbel
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleIntegral
import Mathlib.Tactic

/-! # Cancellation at the lower Gaussian endpoint -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The critical-line phase cancels at the physical
endpoint one, leaving an exponential factor and a difference of resolvents. -/
public theorem gaussian_six_pole_remainder_eq (X : ℝ) (ρ : ℂ) :
    let a : ℝ := 11 / 10
    let z := (21 / 8 : ℝ) + Real.log X
    let s := (a : ℂ) + (ρ.im : ℂ) * Complex.I
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ)
    gaussianSixPoleRemainder X ρ =
      3 * m * (a ^ 5 * Real.exp (-(a * z)) / 120) *
        (gaussianSixPoleAnti s (z : ℂ) - (z : ℂ) ^ 5 / ρ).re := by
  intro a z s m
  let b : ℝ := 21 / 8
  let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
  let D : ℝ := a ^ 5 * Real.exp (-(a * z)) / 120
  let L := Real.log X
  let P := Complex.exp (((ρ.im * L : ℝ) : ℂ) * Complex.I)
  have hE : P * Complex.exp (s * ((b : ℂ) - (z : ℂ))) = (Real.exp (-(a * L)) : ℂ) := by
    unfold P
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    simp only [s, z, b, L, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hD : C * Real.exp (-(a * L)) = D := by
    unfold C D
    rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]
    congr 3
    dsimp only [z, L, b]
    ring
  have hW : quarterWeight656 X 1 = D * z ^ 5 := by
    rw [quarterWeight656, Real.sqrt_one, div_one, one_mul, one_div, Real.log_inv, sub_neg_eq_add]
    dsimp only [D, z, a]
    ring
  have hr (r : ℝ) (w : ℂ) : ((r : ℂ) * w).re = r * w.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp : (m : ℂ) * P * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (z : ℂ))) = (m : ℂ) * (D : ℂ) := by
    rw [show
        (m : ℂ) * P * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (z : ℂ))) =
          (m : ℂ) * ((C : ℂ) * (P * Complex.exp (s * ((b : ℂ) - (z : ℂ)))))
        by ring,
      hE, ← Complex.ofReal_mul, hD]
  change
    3 *
        (((m : ℂ) * P * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (z : ℂ))) *
              gaussianSixPoleAnti s (z : ℂ)).re +
          (-(m : ℂ) / ρ).re * quarterWeight656 X 1) =
      _
  have hdiv (r : ℝ) : ((r : ℂ) / ρ).re = r * ρ⁻¹.re := by rw [div_eq_mul_inv, hr]
  rw [hp, hW, mul_assoc, hr, hr, neg_div, Complex.neg_re, hdiv, Complex.sub_re, ←
    Complex.ofReal_pow, hdiv]
  change _ = 3 * m * D * _
  ring

/-- Cancellation removes the inverse-first-power tail. For critical-line
zeros of ordinate at least one, the remaining terms decay as the inverse square. -/
public theorem gaussian_six_pole_resolvent_norm {ρ : ℂ} (hre : ρ.re = 1 / 2) (hγ : 1 ≤ |ρ.im|)
    {z : ℝ} (hz : 10 ≤ z) :
    let s := ((11 / 10 : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I
    ‖gaussianSixPoleAnti s (z : ℂ) - (z : ℂ) ^ 5 / ρ‖ ≤ (2 * z ^ 5) / |ρ.im| ^ 2 := by
  intro s
  have hz0 : 0 ≤ z := (by norm_num only : (0 : ℝ) ≤ 10).trans hz
  let g := |ρ.im|
  have hg : 0 < g := zero_lt_one.trans_le hγ
  have hρ : g ≤ ‖ρ‖ := Complex.abs_im_le_norm _
  have hs : g ≤ ‖s‖ := by
    have he : s.im = ρ.im := by
      simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
    change |ρ.im| ≤ ‖s‖
    rw [← he]
    exact Complex.abs_im_le_norm _
  have hdiff : ρ - s = -(3 / 5 : ℂ) := by
    rw [← Complex.re_add_im ρ, hre]
    simp only [s, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hden : g ^ 2 ≤ ‖s * ρ‖ := by
    rw [pow_two, norm_mul]
    exact mul_le_mul hs hρ hg.le (norm_nonneg _)
  have hmain : (z : ℂ) ^ 5 / s - (z : ℂ) ^ 5 / ρ = (z : ℂ) ^ 5 * (ρ - s) / (s * ρ) := by
    field_simp [norm_pos_iff.mp (hg.trans_le hs), norm_pos_iff.mp (hg.trans_le hρ)]
  have h₁ : ‖(z : ℂ) ^ 5 / s - (z : ℂ) ^ 5 / ρ‖ ≤ z ^ 5 / g ^ 2 := by
    rw [hmain, hdiff, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hz0]
    have hc : ‖-(3 / 5 : ℂ)‖ ≤ 1 := by
      rw [show -(3 / 5 : ℂ) = ((-(3 / 5 : ℝ) : ℝ) : ℂ) by
          simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat],
        Complex.norm_real, Real.norm_eq_abs]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 5)]
    exact
      div_le_div₀ (pow_nonneg hz0 _)
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (pow_nonneg hz0 _))
        (pow_pos hg _) hden
  have hb (c : ℝ) (hc : 0 ≤ c) {i j : ℕ} (hi : i ≤ 5) (hj : 2 ≤ j) :
    ‖(c : ℂ) * (z : ℂ) ^ i / s ^ j‖ ≤ (c / (10 : ℝ) ^ (5 - i)) * z ^ 5 / g ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hz0]
    have hnum : c * z ^ i ≤ c / (10 : ℝ) ^ (5 - i) * z ^ 5 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos (by norm_num only : (0 : ℝ) < 10) _)]
      calc
        _ ≤ (c * z ^ i) * z ^ (5 - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num only) hz _)
            (mul_nonneg hc (pow_nonneg hz0 _))
        _ = _ := by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
    exact
      div_le_div₀ ((mul_nonneg hc (pow_nonneg hz0 _)).trans hnum) hnum (pow_pos hg _)
        ((pow_le_pow_right₀ hγ hj).trans (pow_le_pow_left₀ hg.le hs _))
  unfold gaussianSixPoleAnti
  rw [show
      (z : ℂ) ^ 5 / s + 5 * (z : ℂ) ^ 4 / s ^ 2 + 20 * (z : ℂ) ^ 3 / s ^ 3 +
            60 * (z : ℂ) ^ 2 / s ^ 4 +
            120 * (z : ℂ) / s ^ 5 +
            120 / s ^ 6 -
          (z : ℂ) ^ 5 / ρ =
        ((z : ℂ) ^ 5 / s - (z : ℂ) ^ 5 / ρ) + 5 * (z : ℂ) ^ 4 / s ^ 2 + 20 * (z : ℂ) ^ 3 / s ^ 3 +
          60 * (z : ℂ) ^ 2 / s ^ 4 +
          120 * (z : ℂ) / s ^ 5 +
          120 / s ^ 6
      by ring]
  have h₂ := hb 5 (by norm_num only) (i := 4) (j := 2) (by decide) (by decide)
  have h₃ := hb 20 (by norm_num only) (i := 3) (j := 3) (by decide) (by decide)
  have h₄ := hb 60 (by norm_num only) (i := 2) (j := 4) (by decide) (by decide)
  have h₅ := hb 120 (by norm_num only) (i := 1) (j := 5) (by decide) (by decide)
  have h₆ := hb 120 (by norm_num only) (i := 0) (j := 6) (by decide) (by decide)
  simp only [Complex.ofReal_ofNat, pow_one, pow_zero, mul_one] at h₂ h₃ h₄ h₅ h₆
  refine
    (norm_add_le _ _).trans
      ((add_le_add
            ((norm_add_le _ _).trans
              (add_le_add
                ((norm_add_le _ _).trans
                  (add_le_add
                    ((norm_add_le _ _).trans
                      (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃))
                    h₄))
                h₅))
            h₆).trans
        ?_)
  norm_num only [Nat.reduceSub, pow_zero, pow_one]
  change _ ≤ 2 * z ^ 5 / g ^ 2
  have hn : 0 ≤ z ^ 5 * g⁻¹ ^ 2 := mul_nonneg (pow_nonneg hz0 _) (sq_nonneg _)
  ring_nf
  nlinarith only [hn]

/-- For logarithmic coordinates at least ten, the endpoint correction decays
exponentially in the logarithmic coordinate, with a summable ordinate factor. -/
public theorem gaussian_six_pole_remainder_bound {X : ℝ} (hX : 10 ≤ (21 / 8 : ℝ) + Real.log X)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) (hγ : 1 ≤ |ρ.im|) :
    let a : ℝ := 11 / 10
    let z := (21 / 8 : ℝ) + Real.log X
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ)
    |gaussianSixPoleRemainder X ρ| ≤
      (3 * (a ^ 5 * Real.exp (-(a * z)) / 120) * (2 * z ^ 5)) * (m / |ρ.im| ^ 2) := by
  intro a z m
  have hz : 10 ≤ z := hX
  let D : ℝ := a ^ 5 * Real.exp (-(a * z)) / 120
  have hD : 0 ≤ D :=
    div_nonneg (mul_nonneg (pow_nonneg (by norm_num only [a]) _) (Real.exp_pos _).le)
      (by norm_num only)
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hp : 0 ≤ 3 * m * D := mul_nonneg (mul_nonneg (by norm_num only) hm) hD
  rw [gaussian_six_pole_remainder_eq]
  change |3 * m * D * _| ≤ 3 * D * (2 * z ^ 5) * (m / |ρ.im| ^ 2)
  rw [abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ 3 * m * D * ((2 * z ^ 5) / |ρ.im| ^ 2) :=
      mul_le_mul_of_nonneg_left
        ((Complex.abs_re_le_norm _).trans (gaussian_six_pole_resolvent_norm hre hγ hz)) hp
    _ = _ := by ring

end PseudoPrime.PrimeTestBounds.MillerRabin
