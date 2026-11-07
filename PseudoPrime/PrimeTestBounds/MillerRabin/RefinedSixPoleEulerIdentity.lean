/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerDerivatives
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedEulerIdentity

/-! # Signed Euler series for the refined sixth-pole operator -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a real argument, the real part of a log-weighted twisted Mangoldt
term equals the corresponding real character weight. The zero index vanishes,
and positive natural bases identify the complex logarithm and power with their
real counterparts. This is the termwise input for the Euler series identity. -/
theorem re_log_mangoldt_term {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (j n : ℕ) :
    (LSeries.term (LSeries.logMul^[j] (fun k : ℕ ↦ χ k * (ArithmeticFunction.vonMangoldt k : ℂ)))
          (σ : ℂ) n).re =
      (Real.log n) ^ j * ((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, Complex.zero_re, ArithmeticFunction.map_zero, mul_zero, zero_div]
  · rw [LSeries.term_of_ne_zero hn,
      AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.logMul_iterate_apply,
      show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm, ←
      Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.div_ofReal_re, ←
      Complex.ofReal_log (Nat.cast_nonneg n)]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    ring

/-- Every log-weighted twisted Mangoldt series at `79/50` converges absolutely.
The standard untwisted logarithmic moment dominates each term. This permits
mapping the series through real part and combining the first three moments. -/
theorem summable_log_mangoldt_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ℕ) :
    Summable
      (fun n : ℕ ↦
        LSeries.term (LSeries.logMul^[j] (fun k : ℕ ↦ χ k * (ArithmeticFunction.vonMangoldt k : ℂ)))
          (79 / 50 : ℂ) n) := by
  apply
    (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 79 / 50)
        (by norm_num only) j).of_norm_bounded
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, zero_mul, zero_div,
      le_refl]
  · have h :=
      AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.twisted_logTerm_bound χ j n (s :=
        (79 / 50 : ℂ)) (Nat.pos_of_ne_zero hn)
    norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat] at h
    exact h

/-- The real part of any iterated ordinary logarithmic derivative at `79/50`
equals its signed real log-weighted Euler series. Absolute convergence and the
termwise real-part identity justify passage to the infinite sum. -/
theorem re_deriv_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ℕ) :
    (iteratedDeriv j (logDeriv χ.LFunction) (79 / 50 : ℂ)).re =
      -((-1 : ℝ) ^ j *
          ∑' n : ℕ,
            (Real.log n) ^ j *
              ((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (79 / 50 : ℝ))) := by
  rw [refined_six_pole_euler_deriv]
  unfold LSeries
  have hc : ((-1 : ℂ) ^ j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_tsum (summable_log_mangoldt_term χ j)]
  congr 2
  apply tsum_congr
  intro n
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using re_log_mangoldt_term χ (79 / 50) j n

/-- The sixth-pole differential combination of the ordinary logarithmic
L-function derivative is exactly negative eight times the signed refined Euler
series. The three absolutely convergent log moments combine termwise into the
nonnegative polynomial weight, preserving the signs of character values. -/
theorem refined_six_euler_operator_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (3 * (logDeriv χ.LFunction (79 / 50 : ℂ)).re -
          (81 / 25 : ℝ) * (deriv (logDeriv χ.LFunction) (79 / 50 : ℂ)).re +
        (729 / 625 : ℝ) * (deriv (deriv (logDeriv χ.LFunction)) (79 / 50 : ℂ)).re) =
      -8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
  let f : ℕ → ℕ → ℝ := fun j n ↦
    (Real.log n) ^ j * ((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (79 / 50 : ℝ))
  have hs (j : ℕ) : Summable (f j) := by
    have h := Complex.reCLM.summable (summable_log_mangoldt_term χ j)
    apply h.congr
    intro n
    simpa only [f, Complex.reCLM_apply, Complex.ofReal_div, Complex.ofReal_ofNat] using
      re_log_mangoldt_term χ (79 / 50) j n
  have h0 := re_deriv_euler χ 0
  have h1 := re_deriv_euler χ 1
  have h2 := re_deriv_euler χ 2
  change
    (iteratedDeriv 0 (logDeriv χ.LFunction) (79 / 50 : ℂ)).re = -((-1 : ℝ) ^ 0 * ∑' n, f 0 n) at h0
  change
    (iteratedDeriv 1 (logDeriv χ.LFunction) (79 / 50 : ℂ)).re = -((-1 : ℝ) ^ 1 * ∑' n, f 1 n) at h1
  change
    (iteratedDeriv 2 (logDeriv χ.LFunction) (79 / 50 : ℂ)).re = -((-1 : ℝ) ^ 2 * ∑' n, f 2 n) at h2
  simp only [iteratedDeriv_zero, iteratedDeriv_succ, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul, neg_neg] at h0 h1 h2
  rw [h0, h1, h2]
  have hsum :
    (∑' n : ℕ, ((3 * f 0 n + (81 / 25 : ℝ) * f 1 n) + (729 / 625 : ℝ) * f 2 n)) =
      3 * (∑' n, f 0 n) + (81 / 25 : ℝ) * (∑' n, f 1 n) + (729 / 625 : ℝ) * (∑' n, f 2 n) := by
    rw [Summable.tsum_add ((hs 0).mul_left 3 |>.add ((hs 1).mul_left (81 / 25)))
        ((hs 2).mul_left (729 / 625)),
      Summable.tsum_add ((hs 0).mul_left 3) ((hs 1).mul_left (81 / 25))]
    simp only [tsum_mul_left]
  have he :
    (∑' n : ℕ, ((3 * f 0 n + (81 / 25 : ℝ) * f 1 n) + (729 / 625 : ℝ) * f 2 n)) =
      8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [f, refinedSixEulerWeight, pow_zero, pow_one]
    ring
  linarith only [hsum, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
