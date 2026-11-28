/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZero570
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleZeroEuler

/-! # Signed Euler series for the section 31 zero mass -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the refined pole distance `51/50`, the corresponding ordinary
L-function point is `38/25`. Every derivative order of its logarithmic
derivative equals the absolutely convergent twisted von Mangoldt L-series
with the matching logarithmic power and sign. Orders zero, one and two are the
Euler inputs to the differentiated sixth-pole identity. -/
theorem quarter_euler_deriv_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    iteratedDeriv n (logDeriv χ.LFunction) (38 / 25 : ℂ) =
      -(((-1 : ℂ) ^ n) *
          LSeries
            (LSeries.logMul^[n]
              (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
            (38 / 25)) := by
  exact
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.iteratedDeriv_euler χ
      (by norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat])
      n

/-- The nonnegative Euler weight produced by the normalized sixth-pole
Poisson differential operator. It combines the three logarithmic powers at
`σ=38/25`; the factor `1/8` matches the actual kernel normalization. -/
noncomputable def quarterEulerWeight570 (n : ℕ) : ℝ :=
  (3 + (153 / 50 : ℝ) * Real.log n + (2601 / 2500 : ℝ) * (Real.log n) ^ 2) /
    (8 * (n : ℝ) ^ (38 / 25 : ℝ))

/-- For positive natural indices, the refined Euler weight is nonnegative.
Its numerator is a positive polynomial in the nonnegative logarithm. -/
theorem quarter_euler_weight_nonneg_570 {n : ℕ} (hn : 1 ≤ n) : 0 ≤ quarterEulerWeight570 n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := Real.log_nonneg hnR
  unfold quarterEulerWeight570
  apply div_nonneg
  · nlinarith only [hl, sq_nonneg (Real.log n)]
  · exact mul_nonneg (by norm_num only) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The universal von Mangoldt series weighted by the refined Euler weight
is summable. Expand the polynomial into the established convergent logarithmic
moments of orders zero, one and two. This supplies convergence for later
signed character sums and finite-prefix comparisons. -/
theorem quarter_euler_weight_summable_570 :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  have h0 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only) 0
  have h1 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only) 1
  have h2 :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only) 2
  have hs :=
    (((h0.mul_left 3).add (h1.mul_left (153 / 50))).add (h2.mul_left (2601 / 2500))).mul_left
      (1 / 8 : ℝ)
  apply hs.congr
  intro n
  simp only [quarterEulerWeight570, pow_zero, pow_one]
  ring

/-- The refined Euler weight is nonnegative at every natural index, including
zero. The natural-number logarithm and the real-power denominator are
nonnegative under Lean's total conventions. -/
theorem quarter_euler_weight_nonneg_570_all (n : ℕ) : 0 ≤ quarterEulerWeight570 n := by
  have hl := Real.log_natCast_nonneg n
  unfold quarterEulerWeight570
  apply div_nonneg
  · nlinarith only [hl, sq_nonneg (Real.log n)]
  · exact mul_nonneg (by norm_num only) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- For any Dirichlet character, the refined signed Euler series is absolutely
summable. The universal nonnegative Mangoldt weight dominates each real
character value. This permits the three-character finite-prefix comparison. -/
theorem quarter_signed_euler_summable_570 {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Summable
      (fun n : ℕ ↦ (χ n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n)) := by
  apply quarter_euler_weight_summable_570.of_norm_bounded
  intro n
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n :=
    mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
      (quarter_euler_weight_nonneg_570_all n)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  have hc := (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hw

/-- Every log-weighted twisted Mangoldt series at `38/25` converges absolutely.
The standard untwisted logarithmic moment dominates each term. This permits
mapping the series through real part and combining the first three moments. -/
theorem quarter_log_term_summable_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ℕ) :
    Summable
      (fun n : ℕ ↦
        LSeries.term (LSeries.logMul^[j] (fun k : ℕ ↦ χ k * (ArithmeticFunction.vonMangoldt k : ℂ)))
          (38 / 25 : ℂ) n) := by
  apply
    (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
        (by norm_num only) j).of_norm_bounded
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, zero_mul, zero_div,
      le_refl]
  · have h :=
      AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.twisted_logTerm_bound χ j n (s :=
        (38 / 25 : ℂ)) (Nat.pos_of_ne_zero hn)
    norm_num only [Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat] at h
    exact h

/-- The real part of any iterated ordinary logarithmic derivative at `38/25`
equals its signed real log-weighted Euler series. Absolute convergence and the
termwise real-part identity justify passage to the infinite sum. -/
theorem quarter_re_euler_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ℕ) :
    (iteratedDeriv j (logDeriv χ.LFunction) (38 / 25 : ℂ)).re =
      -((-1 : ℝ) ^ j *
          ∑' n : ℕ,
            (Real.log n) ^ j *
              ((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ))) := by
  rw [quarter_euler_deriv_570]
  unfold LSeries
  have hc : ((-1 : ℂ) ^ j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_tsum (quarter_log_term_summable_570 χ j)]
  congr 2
  apply tsum_congr
  intro n
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using re_log_mangoldt_term χ (38 / 25) j n

/-- The sixth-pole differential combination of the ordinary logarithmic
L-function derivative is exactly negative eight times the signed refined Euler
series. The three absolutely convergent log moments combine termwise into the
nonnegative polynomial weight, preserving the signs of character values. -/
theorem quarter_euler_operator_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (3 * (logDeriv χ.LFunction (38 / 25 : ℂ)).re -
          (153 / 50 : ℝ) * (deriv (logDeriv χ.LFunction) (38 / 25 : ℂ)).re +
        (2601 / 2500 : ℝ) * (deriv (deriv (logDeriv χ.LFunction)) (38 / 25 : ℂ)).re) =
      -8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  let f : ℕ → ℕ → ℝ := fun j n ↦
    (Real.log n) ^ j * ((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ))
  have hs (j : ℕ) : Summable (f j) := by
    have h := Complex.reCLM.summable (quarter_log_term_summable_570 χ j)
    apply h.congr
    intro n
    simpa only [f, Complex.reCLM_apply, Complex.ofReal_div, Complex.ofReal_ofNat] using
      re_log_mangoldt_term χ (38 / 25) j n
  have h0 := quarter_re_euler_570 χ 0
  have h1 := quarter_re_euler_570 χ 1
  have h2 := quarter_re_euler_570 χ 2
  change
    (iteratedDeriv 0 (logDeriv χ.LFunction) (38 / 25 : ℂ)).re = -((-1 : ℝ) ^ 0 * ∑' n, f 0 n) at h0
  change
    (iteratedDeriv 1 (logDeriv χ.LFunction) (38 / 25 : ℂ)).re = -((-1 : ℝ) ^ 1 * ∑' n, f 1 n) at h1
  change
    (iteratedDeriv 2 (logDeriv χ.LFunction) (38 / 25 : ℂ)).re = -((-1 : ℝ) ^ 2 * ∑' n, f 2 n) at h2
  simp only [iteratedDeriv_zero, iteratedDeriv_succ, pow_zero, pow_one, neg_one_sq, one_mul,
    neg_one_mul, neg_neg] at h0 h1 h2
  rw [h0, h1, h2]
  have hsum :
    (∑' n : ℕ, ((3 * f 0 n + (153 / 50 : ℝ) * f 1 n) + (2601 / 2500 : ℝ) * f 2 n)) =
      3 * (∑' n, f 0 n) + (153 / 50 : ℝ) * (∑' n, f 1 n) + (2601 / 2500 : ℝ) * (∑' n, f 2 n) := by
    rw [Summable.tsum_add ((hs 0).mul_left 3 |>.add ((hs 1).mul_left (153 / 50)))
        ((hs 2).mul_left (2601 / 2500)),
      Summable.tsum_add ((hs 0).mul_left 3) ((hs 1).mul_left (153 / 50))]
    simp only [tsum_mul_left]
  have he :
    (∑' n : ℕ, ((3 * f 0 n + (153 / 50 : ℝ) * f 1 n) + (2601 / 2500 : ℝ) * f 2 n)) =
      8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [f, quarterEulerWeight570, pow_zero, pow_one]
    ring
  linarith only [hsum, he]

/-- For a nonprincipal character, the real-variable differential operator
on the ordinary logarithmic L-derivative equals the signed refined Euler
series. Analyticity on the half-line converts real derivatives to complex
derivatives, to which the exact Euler identity applies. -/
theorem quarter_real_euler_operator_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) :
    let f : ℝ → ℝ := fun u ↦ (logDeriv χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
    3 * f (51 / 50) - (153 / 50 : ℝ) * deriv f (51 / 50) +
        (2601 / 2500 : ℝ) * deriv (deriv f) (51 / 50) =
      -8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  have hf (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv χ.LFunction) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    have ha := (χ.differentiable_LFunction hne).analyticAt (((1 / 2 : ℝ) + u : ℝ) : ℂ)
    have hn : χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ) ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
      simp only [Complex.ofReal_re]
      linarith only [hu]
    exact ha.deriv.div ha hn
  have ha : (1 / 2 : ℝ) < 51 / 50 := by norm_num only
  have hc : (((1 / 2 : ℝ) + 51 / 50 : ℝ) : ℂ) = (38 / 25 : ℂ) := by
    norm_num only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hd := (hf (51 / 50) ha).differentiableAt.hasDerivAt.real_of_complex
  have hd' := hd.comp (51 / 50 : ℝ) ((hasDerivAt_id (51 / 50 : ℝ)).const_add (1 / 2 : ℝ))
  have hd1 :
    deriv (fun u : ℝ ↦ (logDeriv χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re) (51 / 50) =
      (deriv (logDeriv χ.LFunction) (38 / 25 : ℂ)).re := by
    simpa only [mul_one, Function.comp_def, hc] using hd'.deriv
  have hd2 := real_shift_derivs (logDeriv χ.LFunction) ha hf
  rw [hc] at hd2
  change 3 * (logDeriv χ.LFunction (((1 / 2 : ℝ) + 51 / 50 : ℝ) : ℂ)).re - _ + _ = _
  rw [hc, hd1, hd2]
  exact quarter_euler_operator_570 χ

/-- Under individual RH, the normalized sixth-pole zero mass equals its
conductor term and the explicit Gamma differential expression minus the
signed refined Euler series. The Poisson formula, analytic derivative
splitting, and the Euler identity retain the signs needed for the subsequent
three-character prefix estimate. -/
theorem quarter_zero_euler_570 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    let G : ℝ → ℝ := fun u ↦ (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖quarterKernel570.function (Complex.I * ρ.im)‖) =
      (3 / 2 : ℝ) * Real.log q + 3 * G (51 / 50) - (153 / 50 : ℝ) * deriv G (51 / 50) +
          (2601 / 2500 : ℝ) * deriv (deriv G) (51 / 50) -
        8 * ∑' n : ℕ, (χ n).re * (ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) := by
  have hf (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv χ.gammaFactor) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    have hs : 0 < ((((1 / 2 : ℝ) + u : ℝ) : ℂ)).re := by
      simp only [Complex.ofReal_re]
      linarith only [hu]
    have h := AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ hs
    exact h.deriv.div h (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hs)
  have hg (u : ℝ) (hu : 1 / 2 < u) :
    AnalyticAt ℂ (logDeriv χ.LFunction) (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by
    have ha := (χ.differentiable_LFunction hne).analyticAt (((1 / 2 : ℝ) + u : ℝ) : ℂ)
    have hn : χ.LFunction (((1 / 2 : ℝ) + u : ℝ) : ℂ) ≠ 0 := by
      apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne)
      simp only [Complex.ofReal_re]
      linarith only [hu]
    exact ha.deriv.div ha hn
  have ha : (1 / 2 : ℝ) < 51 / 50 := by norm_num only
  have hd := real_shift_sum_derivs (logDeriv χ.gammaFactor) (logDeriv χ.LFunction) ha hf hg
  have h := quarter_conductor_formula_570 hq hRH hp hne hinv
  have he := quarter_real_euler_operator_570 χ hne
  change _ = _ at he
  change _ = _ at h
  unfold refinedPoissonRemainder at h
  rw [hd.1, hd.2] at h
  norm_num only at h
  linarith only [h, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
