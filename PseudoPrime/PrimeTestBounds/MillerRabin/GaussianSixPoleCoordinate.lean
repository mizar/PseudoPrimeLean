/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import Mathlib.Tactic

/-! # Logarithmic coordinates for the shared six-pole Gaussian kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Reverse the logarithmic coordinate from the support endpoint to the physical argument. -/
@[expose]
public noncomputable def gaussianSixPoleCoord (X t : ℝ) : ℝ :=
  21 / 8 - Real.log (t / X)

/-- Express the physical weight times an RH zero term as a normalized exponential
polynomial in the support coordinate. The Jacobian is retained on the right. -/
public theorem gaussian_six_pole_zero_coord {X t : ℝ} (hX : 0 < X) (ht : 0 < t) (c : ℂ) (γ : ℝ) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    let v := gaussianSixPoleCoord X t
    let s := (a : ℂ) + (γ : ℂ) * Complex.I
    let p := c * Complex.exp (((γ * Real.log X : ℝ) : ℂ) * Complex.I)
    quarterWeight656 X t * ((c * (t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re / t) =
      (p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (v : ℂ))) * (v : ℂ) ^ 5).re / t := by
  intro a b C v s p
  have hv : b - v = Real.log t - Real.log X := by
    simp only [v, b, gaussianSixPoleCoord, sub_sub_cancel, Real.log_div ht.ne' hX.ne']
  have hphase :
    (t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) =
      (Real.sqrt t : ℂ) * Complex.exp (((γ * Real.log t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), ← Complex.ofReal_log ht.le,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_mul]
    ring
  have he :
    Complex.exp (s * ((b : ℂ) - (v : ℂ))) =
      (Real.exp (a * (b - v)) : ℂ) *
        Complex.exp (((γ * (Real.log t - Real.log X) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_sub, ← hv]
    simp only [s, Complex.ofReal_mul]
    ring
  have hC : C * Real.exp (a * (b - v)) = a ^ 5 * Real.exp (-(a * v)) / 120 := by
    dsimp only [C]
    rw [div_mul_eq_mul_div, mul_assoc, ← Real.exp_add]
    congr 3
    ring
  have hc :
    (c * Complex.exp (((γ * Real.log X : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((γ * (Real.log t - Real.log X) : ℝ) : ℂ) * Complex.I) =
      c * Complex.exp (((γ * Real.log t : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  rw [hphase, he]
  unfold quarterWeight656
  change (1 / Real.sqrt t) * ((a * v) ^ 5 * Real.exp (-(a * v)) / 120) * _ = _
  have hr (r : ℝ) (w : ℂ) : ((r : ℂ) * w).re = r * w.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hright :
    p * (C : ℂ) *
        ((Real.exp (a * (b - v)) : ℂ) *
          Complex.exp (((γ * (Real.log t - Real.log X) : ℝ) : ℂ) * Complex.I)) *
        (v : ℂ) ^ 5 =
      ((C * Real.exp (a * (b - v)) * v ^ 5 : ℝ) : ℂ) *
        (c * Complex.exp (((γ * Real.log t : ℝ) : ℂ) * Complex.I)) := by
    rw [← hc]
    simp only [p, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [hright, hr, hC, mul_left_comm c (Real.sqrt t : ℂ), hr]
  field_simp [(Real.sqrt_pos.2 ht).ne', ht.ne']

/-- Transform the physical zero integral on a positive interval to the
reversed logarithmic coordinate. -/
public theorem gaussian_six_pole_zero_integral {X l r : ℝ} (hX : 0 < X) (hl : 0 < l) (hlr : l ≤ r)
    (c : ℂ) (γ : ℝ) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    let s := (a : ℂ) + (γ : ℂ) * Complex.I
    let p := c * Complex.exp (((γ * Real.log X : ℝ) : ℂ) * Complex.I)
    let g := fun v : ℝ ↦ (p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (v : ℂ))) * (v : ℂ) ^ 5).re
    (∫ t in l..r,
        quarterWeight656 X t * ((c * (t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re / t)) =
      ∫ v in gaussianSixPoleCoord X r..gaussianSixPoleCoord X l, g v := by
  intro a b C s p g
  have hp (t : ℝ) (ht : t ∈ Set.uIcc l r) : 0 < t := hl.trans_le (Set.uIcc_of_le hlr ▸ ht).1
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt (gaussianSixPoleCoord X) (-t⁻¹) t := by
    have hh := (Real.hasDerivAt_log (x := t) ht.ne').const_sub (21 / 8)
    have hh' := hh.add_const (Real.log X)
    apply hh'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    rw [gaussianSixPoleCoord, Real.log_div (show 0 < u from hu).ne' hX.ne']
    ring
  have hc : ContinuousOn (fun t : ℝ ↦ -t⁻¹) (Set.uIcc l r) :=
    (continuousOn_id.inv₀ (fun t ht ↦ (hp t ht).ne')).neg
  have hg : Continuous g :=
    Complex.continuous_re.comp
      ((continuous_const.mul
            (Complex.continuous_exp.comp
              (continuous_const.mul (continuous_const.sub Complex.continuous_ofReal)))).mul
        (Complex.continuous_ofReal.pow 5))
  have h :=
    intervalIntegral.integral_comp_mul_deriv' (a := l) (b := r) (f := gaussianSixPoleCoord X) (f' :=
      fun t ↦ -t⁻¹) (g := g) (fun t ht ↦ hd t (hp t ht)) hc hg.continuousOn
  rw [intervalIntegral.integral_symm (f := g) (gaussianSixPoleCoord X r)
      (gaussianSixPoleCoord X l)] at h
  simp only [Function.comp_def, mul_neg, intervalIntegral.integral_neg, neg_inj] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t ht
  change _ = g (gaussianSixPoleCoord X t) * t⁻¹
  rw [← div_eq_mul_inv]
  exact gaussian_six_pole_zero_coord hX (hp t ht) c γ

/-- Evaluate the physical Mellin integrals on the two sides of the cutoff.
The lower endpoint remains explicit, ready for the zero-sum error estimate. -/
public theorem gaussian_six_pole_physical_integrals {X : ℝ} (hX : 1 ≤ X) (c : ℂ) {γ : ℝ}
    (hγ : γ ≠ 0) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
    let s := (a : ℂ) + (γ : ℂ) * Complex.I
    let p := c * Complex.exp (((γ * Real.log X : ℝ) : ℂ) * Complex.I)
    let U := X * Real.exp b
    let z := b + Real.log X
    let f := fun t : ℝ ↦ quarterWeight656 X t * ((c * (t : ℂ) ^ ρ).re / t)
    (p * (4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ)).re - 3 * (∫ t in (1 : ℝ)..X, f t) + (∫ t in X..U, f t) =
      (p * gaussianSpectralCoeff γ).re +
        3 *
          (p * (C : ℂ) * Complex.exp (s * ((b : ℂ) - (z : ℂ))) *
              gaussianSixPoleAnti s (z : ℂ)).re := by
  intro a b C ρ s p U z f
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hU : X ≤ U := le_mul_of_one_le_right hX0.le (Real.one_le_exp (by norm_num only [b]))
  have hcoX : gaussianSixPoleCoord X X = b := by
    rw [gaussianSixPoleCoord, div_self hX0.ne', Real.log_one, sub_zero]
  have hcoU : gaussianSixPoleCoord X U = 0 := by
    rw [gaussianSixPoleCoord, show U = Real.exp b * X from mul_comm _ _,
      mul_div_cancel_right₀ _ hX0.ne', Real.log_exp]
    exact sub_self b
  have hco1 : gaussianSixPoleCoord X 1 = z := by
    rw [gaussianSixPoleCoord, one_div, Real.log_inv, sub_neg_eq_add]
  have h₁ := gaussian_six_pole_zero_integral hX0 zero_lt_one hX c γ
  have h₂ := gaussian_six_pole_zero_integral hX0 hX0 hU c γ
  dsimp only at h₁ h₂
  rw [hcoX, hco1] at h₁
  rw [hcoX, hcoU] at h₂
  change
    (p * (4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ)).re - 3 * (∫ t in (1 : ℝ)..X, f t) + (∫ t in X..U, f t) = _
  dsimp only [f, ρ]
  rw [h₁, h₂]
  exact gaussian_six_pole_spectral_integral hγ p z

/-- Identify the normalized cutoff term with the physical weight at the cutoff. -/
public theorem gaussian_six_pole_zero_cutoff {X : ℝ} (hX : 0 < X) (c : ℂ) (γ : ℝ) :
    let a : ℝ := 11 / 10
    let b : ℝ := 21 / 8
    let C : ℝ := a ^ 5 * Real.exp (-(a * b)) / 120
    let ρ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I
    let p := c * Complex.exp (((γ * Real.log X : ℝ) : ℂ) * Complex.I)
    4 * quarterWeight656 X X * ((c / ρ) * (X : ℂ) ^ ρ).re =
      (p * (4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ)).re := by
  intro a b C ρ p
  have h := gaussian_six_pole_zero_coord hX hX (c / ρ) γ
  dsimp only at h
  simp only [gaussianSixPoleCoord, div_self hX.ne', Real.log_one, sub_zero, sub_self, mul_zero,
    Complex.exp_zero, mul_one] at h
  have hh := congrArg (fun u : ℝ ↦ u * X) h
  rw [mul_assoc, div_mul_cancel₀ _ hX.ne', div_mul_cancel₀ _ hX.ne'] at hh
  have he :
    p * (4 * ((C * b ^ 5 : ℝ) : ℂ) / ρ) =
      (4 : ℂ) *
        ((c / ρ) * Complex.exp (((γ * Real.log X : ℝ) : ℂ) * Complex.I) * (C : ℂ) *
          (b : ℂ) ^ 5) := by
    simp only [p, Complex.ofReal_mul, Complex.ofReal_pow, div_eq_mul_inv]
    ring
  rw [he, mul_assoc, hh]
  symm
  have h4 (w : ℂ) : (4 * w).re = 4 * w.re := by
    change (((4 : ℝ) : ℂ) * w).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [h4]

end PseudoPrime.PrimeTestBounds.MillerRabin
