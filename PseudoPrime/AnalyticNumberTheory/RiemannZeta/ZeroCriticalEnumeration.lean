/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum

/-! # Critical-line enumerations of positive zeta zeros -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- An enumeration of positive ordinates whose critical-line points are
zeros, and which covers every positive zero through `T`, enumerates exactly
the positive part of the closed-height ledger. -/
theorem positive_ledger_of_ordinates {T : ℝ} (hT : 0 ≤ T) {n : ℕ} (g : Fin n → ℝ)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ T)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcomplete :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          0 < ρ.im → ρ.im ≤ T → ∃ i, ρ = ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) :
    (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) =
      Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) := by
  apply positive_ledger_eq_image
  · intro i
    have hre : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).re = 1 / 2 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him : (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I).im = g i := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    constructor
    · apply (mem_zerosUpTo hT).2
      refine ⟨hzero i, ?_, ?_⟩
      · rw [hre]
        norm_num only
      · rw [him, abs_of_pos (hpos i)]
        exact hheight i
    · rw [him]
      exact hpos i
  · intro ρ hρ hp
    have hz := (mem_zerosUpTo hT).1 hρ
    exact hcomplete ρ hz.1 hp ((le_abs_self ρ.im).trans hz.2.2)

/-- An injective ordinate map gives an injective map to its critical-line
points. Taking imaginary parts transfers equality back to the ordinates. -/
theorem critical_points_injective {n : ℕ} (g : Fin n → ℝ) (hg : Function.Injective g) :
    Function.Injective (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) := by
  intro i j h
  apply hg
  have him := congrArg Complex.im h
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] using him

/-- A zeta zero of analytic order one has multiplicity one in the finite zero
ledger. This converts the order supplied by zero certificates to the counting
API used by reciprocal sums. -/
theorem zeroMultiplicity_eq_one {ρ : ℂ} (h : analyticOrderAt riemannZeta ρ = 1) :
    riemannZetaZeroMultiplicity ρ = 1 := by
  rw [riemannZetaZeroMultiplicity, analyticOrderNatAt, h]
  rfl

/-- For a nonnegative ordinate `t`, the distance from its critical-line
point to one is at most `t + 1/2`. This elementary triangle bound transfers
upper ordinate brackets to the midpoint-rule remainder. -/
theorem critical_point_sub_one_norm_le {t : ℝ} (ht : 0 ≤ t) :
    ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ t + 1 / 2 := by
  have he :
    (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1 =
      ((-(1 / 2 : ℝ) : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he]
  have h := norm_add_le (((-(1 / 2 : ℝ) : ℝ) : ℂ)) ((t : ℂ) * Complex.I)
  simpa only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_mul, Complex.norm_I, mul_one,
    abs_of_nonneg ht, abs_neg, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2), add_comm] using h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
