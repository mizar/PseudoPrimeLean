/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSignedPoisson
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives

/-! # Euler derivatives at the refined sixth-pole point -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the refined pole distance `27/25`, the corresponding ordinary
L-function point is `79/50`. Every derivative order of its logarithmic
derivative equals the absolutely convergent twisted von Mangoldt L-series
with the matching logarithmic power and sign. Orders zero, one and two are the
Euler inputs to the differentiated sixth-pole identity. -/
theorem refined_six_pole_euler_deriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    iteratedDeriv n (logDeriv χ.LFunction) (79 / 50 : ℂ) =
      -(((-1 : ℂ) ^ n) *
          LSeries
            (LSeries.logMul^[n]
              (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
            (79 / 50)) := by
  exact
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.iteratedDeriv_euler χ
      (by norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat])
      n

/-- The nonnegative Euler weight produced by the normalized sixth-pole
Poisson differential operator. It combines the three logarithmic powers at
`σ=79/50`; the factor `1/8` matches the actual kernel normalization. -/
noncomputable def refinedSixEulerWeight (n : ℕ) : ℝ :=
  (3 + (81 / 25 : ℝ) * Real.log n + (729 / 625 : ℝ) * (Real.log n) ^ 2) /
    (8 * (n : ℝ) ^ (79 / 50 : ℝ))

/-- For positive natural indices, the refined Euler weight is nonnegative.
Its numerator is a positive polynomial in the nonnegative logarithm. -/
theorem refined_six_euler_weight_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ refinedSixEulerWeight n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_nonneg hnR
  unfold refinedSixEulerWeight
  apply div_nonneg
  · nlinarith only [hl, sq_nonneg (Real.log n)]
  · exact mul_nonneg (by norm_num only) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The universal von Mangoldt series weighted by the refined Euler weight
is summable. Expand the polynomial into the established convergent logarithmic
moments of orders zero, one and two. This supplies convergence for later
signed character sums and finite-prefix comparisons. -/
theorem refined_six_euler_weight_summable :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) := by
  have h0 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 79 / 50)
      (by norm_num only) 0
  have h1 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 79 / 50)
      (by norm_num only) 1
  have h2 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 79 / 50)
      (by norm_num only) 2
  have hs :=
    (((h0.mul_left 3).add (h1.mul_left (81 / 25))).add (h2.mul_left (729 / 625))).mul_left
      (1 / 8 : ℝ)
  apply hs.congr
  intro n
  simp only [refinedSixEulerWeight, pow_zero, pow_one]
  ring

/-- The refined Euler weight is nonnegative at every natural index, including
zero. The natural-number logarithm and the real-power denominator are
nonnegative under Lean's total conventions. -/
theorem refined_six_euler_weight_nonneg_all (n : ℕ) : 0 ≤ refinedSixEulerWeight n := by
  have hl := Real.log_natCast_nonneg n
  unfold refinedSixEulerWeight
  apply div_nonneg
  · nlinarith only [hl, sq_nonneg (Real.log n)]
  · exact mul_nonneg (by norm_num only) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- For any Dirichlet character, the refined signed Euler series is absolutely
summable. The universal nonnegative Mangoldt weight dominates each real
character value. This permits the three-character finite-prefix comparison. -/
theorem refined_six_euler_signed_summable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Summable
      (fun n : ℕ ↦ (χ n).re * (ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n)) := by
  apply refined_six_euler_weight_summable.of_norm_bounded
  intro n
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n :=
    mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      (refined_six_euler_weight_nonneg_all n)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  have hc := (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hw

end PseudoPrime.PrimeTestBounds.MillerRabin
