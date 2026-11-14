/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadMidpoint

/-! # Midpoint approximation of the signed low-zero sum under RH -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the multiplicity-weighted sum of the distances of zeros
through height A from one is at most `(A + 1/2) * zeroCount A`.
The critical-line identity and the height cutoff bound each term. -/
theorem zero_head_distance_le_count (hRH : RiemannHypothesis) {A : ℝ} (hA : 0 ≤ A) :
    (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) ≤
      (A + 1 / 2) * zeroCount A := by
  have hpoint (ρ : ℂ) (hρ : ρ ∈ zerosUpTo A) : ‖ρ - 1‖ ≤ A + 1 / 2 := by
    have hz := (mem_zerosUpTo hA).1 hρ
    have hr :=
      RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
        (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
    have hn := Complex.norm_le_abs_re_add_abs_im (ρ - 1)
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero, hr] at hn
    norm_num only at hn
    linarith only [hn, hz.2.2]
  rw [zeroCount_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  have h :=
    mul_le_mul_of_nonneg_left (hpoint ρ hρ)
      (show (0 : ℝ) ≤ (riemannZetaZeroMultiplicity ρ : ℝ) from Nat.cast_nonneg _)
  nlinarith only [h]

/-- Under RH, approximate the multiplicity-weighted contribution of all
zeros up to height A by the midpoint value of its signed sum. The error is
controlled by the weighted sum of distances from 1 and the left endpoint. -/
theorem zero_head_midpoint_error (hRH : RiemannHypothesis) {A a b : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hab : a ≤ b) :
    |(∑ ρ ∈ zerosUpTo A,
              (riemannZetaZeroMultiplicity ρ : ℂ) *
                (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))).re -
          (b - a) *
            (∑ ρ ∈ zerosUpTo A,
                (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((a + b) / 2) : ℂ) ^ ρ / ρ)).re| ≤
      (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) * a ^ (-(3 / 2 : ℝ)) *
          (b - a) ^ 3 /
        24 := by
  have hr : ∀ ρ ∈ zerosUpTo A, ρ.re = 1 / 2 := by
    intro ρ hρ
    have hz := (mem_zerosUpTo hA).1 hρ
    exact
      RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH
        (RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2.1)
  have h :=
    weighted_head_midpoint_error (zerosUpTo A) (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ))
      (fun ρ hρ ↦ Nat.cast_nonneg _) hr ha hab
  simpa only [Complex.ofReal_natCast] using h

/-- Under RH, a bound on the midpoint head and a bound on its weighted
distance sum control the integrated head on a positive ordered interval.
This is the form used by the symmetric Chebyshev smoothing estimate. -/
theorem zero_head_integral_le_midpoint (hRH : RiemannHypothesis) {A a b M C : ℝ} (hA : 0 ≤ A)
    (ha : 0 < a) (hab : a ≤ b)
    (hM : (∑ ρ ∈ zerosUpTo A, (riemannZetaZeroMultiplicity ρ : ℝ) * ‖ρ - 1‖) ≤ M)
    (hC :
      |(∑ ρ ∈ zerosUpTo A,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((a + b) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C) :
    |(∑ ρ ∈ zerosUpTo A,
            (riemannZetaZeroMultiplicity ρ : ℂ) *
              (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))).re| ≤
      (b - a) * (C + M * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 2 / 24) := by
  have h := abs_le.mp (zero_head_midpoint_error hRH hA ha hab)
  have hc := abs_le.mp hC
  have hw : 0 ≤ b - a := sub_nonneg.mpr hab
  have hf : 0 ≤ a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 3 / 24 := by
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg ha.le _) (pow_nonneg hw _)) (by norm_num only)
  have hm := mul_le_mul_of_nonneg_right hM hf
  have hcl := mul_le_mul_of_nonneg_left hc.1 hw
  have hcu := mul_le_mul_of_nonneg_left hc.2 hw
  apply abs_le.mpr
  constructor <;> nlinarith only [h.1, h.2, hcl, hcu, hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
