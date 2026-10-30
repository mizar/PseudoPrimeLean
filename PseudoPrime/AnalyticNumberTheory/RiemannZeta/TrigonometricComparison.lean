/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!
# The nonnegative three-four-one zeta comparison

The absolutely convergent Mangoldt series supplies the Euler side of the classical
zero-free-region argument. No zero-free strip or prime-number-theorem error is assumed.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta
/-- For real sigma and height t, the real part of each Mangoldt Dirichlet term is its
cosine weight. Expand the complex power at positive integers; the zero term vanishes.
This identity transfers the Euler series to the real trigonometric comparison. -/
theorem vonMangoldt_term_re (σ t : ℝ) (n : ℕ) :
    (LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ))
      ((σ : ℂ) + t * Complex.I) n).re =
      ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ * Real.cos (t * Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, Complex.zero_re, ArithmeticFunction.map_zero,
      CharP.cast_eq_zero, zero_div, zero_mul]
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  rw [mul_neg, mul_neg, Real.cos_neg, mul_comm (Real.log (n : ℝ)) t,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)), Real.exp_neg]
  ring
/-- For sigma greater than one and any real height, the negative real zeta logarithmic
derivative equals the absolutely convergent cosine-weighted Mangoldt series. Take real parts
of the Euler identity and commute the continuous real projection with the sum.
The identity supplies the analytic side of the three-four-one comparison. -/
theorem neg_re_logDeriv_eq_cos_sum {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    -(logDeriv riemannZeta ((σ : ℂ) + t * Complex.I)).re =
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ *
        Real.cos (t * Real.log n) := by
  have hs : 1 < ((σ : ℂ) + t * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσ
  have h := congrArg Complex.re
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)
  rw [neg_div, Complex.neg_re] at h
  rw [logDeriv, Pi.div_apply, ← h, LSeries, Complex.re_tsum
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
  exact tsum_congr (vonMangoldt_term_re σ t)
/-- For sigma greater than one and any real height, the cosine-weighted Mangoldt series
is summable. Project the absolutely convergent complex Euler series to its real part.
This permits termwise addition in the zero-free-region trigonometric argument. -/
theorem summable_vonMangoldt_cos {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ *
      Real.cos (t * Real.log n)) := by
  have hs : 1 < ((σ : ℂ) + t * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hσ
  exact ((Complex.reCLM.hasSum
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum).summable).congr
      (vonMangoldt_term_re σ t)
/-- At every real phase, the three-four-one cosine polynomial is nonnegative.
The double-angle identity reduces it to twice the square of one plus cosine.
This pointwise certificate gives a nonnegative Mangoldt-weighted series. -/
theorem three_four_one_cos_nonneg (u : ℝ) : 0 ≤ 3 + 4 * Real.cos u + Real.cos (2*u) := by
  rw [Real.cos_two_mul]
  nlinarith only [sq_nonneg (Real.cos u + 1)]
/-- For sigma greater than one and arbitrary real height t, the three-four-one
combination of negative real zeta logarithmic derivatives at heights zero, t, and twice t
is nonnegative. Sum the pointwise cosine certificate using absolute convergence.
This unconditional inequality is the Euler-side input for a quantitative zero-free region. -/
theorem three_four_one_logDeriv_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ -3 * (logDeriv riemannZeta (σ : ℂ)).re -
      4 * (logDeriv riemannZeta ((σ : ℂ) + t * Complex.I)).re -
      (logDeriv riemannZeta ((σ : ℂ) + (2*t) * Complex.I)).re := by
  have hz := neg_re_logDeriv_eq_cos_sum hσ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero, mul_one] at hz
  have ht := neg_re_logDeriv_eq_cos_sum hσ t
  have h2 := neg_re_logDeriv_eq_cos_sum hσ (2*t)
  have hs0 := summable_vonMangoldt_div_rpow hσ
  have hs1 := summable_vonMangoldt_cos hσ t
  have hs2 := summable_vonMangoldt_cos hσ (2*t)
  have hp : 0 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ *
      (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n))) :=
    tsum_nonneg fun n ↦ mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
      (three_four_one_cos_nonneg _)
  have heq : (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ *
      (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n)))) =
      (fun n ↦ 3 * (ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ) +
      4 * (ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ * Real.cos (t * Real.log n)) +
      ArithmeticFunction.vonMangoldt n / (n : ℝ)^σ * Real.cos ((2*t) * Real.log n)) := by
    funext n
    rw [mul_assoc 2 t (Real.log n)]
    ring
  rw [heq, ((hs0.mul_left 3).add (hs1.mul_left 4)).tsum_add hs2,
    (hs0.mul_left 3).tsum_add (hs1.mul_left 4), hs0.tsum_mul_left 3,
    hs1.tsum_mul_left 4, ← hz, ← ht, ← h2] at hp
  norm_num only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hp
  nlinarith only [hp]
end PseudoPrime.AnalyticNumberTheory.RiemannZeta
