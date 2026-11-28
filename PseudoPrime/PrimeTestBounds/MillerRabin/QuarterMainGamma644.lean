/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainEuler644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainEuler644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrimeContour570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSlope644
public import PseudoPrime.Analysis.ExponentialMomentTail
import Mathlib.Analysis.SumIntegralComparisons

/-! # Archimedean terms of the section 122 main kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The ordinary reflected logarithmic derivative against the sixth-pole
left-line weight is integrable at every positive scale. Sum the integrable
Dirichlet terms using the absolute integrated-norm bound. -/
theorem quarter_ordinary_integrable_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let W := fun t : ℝ ↦
    quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hd : quarterKernel644.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hiW : MeasureTheory.Integrable W := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip quarterKernel644 (c :=
        (-9 / 16 : ℝ)) (u := x⁻¹)
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) (inv_pos.mpr hx)
    simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
      inv_inv] at h
    exact h
  let f := fun n : ℕ ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
  let F := fun (n : ℕ) (t : ℝ) ↦ LSeries.term f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * W t
  have hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have hi :=
    Analysis.integrable_tsum_of_summable_integral_norm F
      (fun n ↦
        AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight f (17 / 16) n
          (fun t : ℝ ↦ -t) continuous_neg W hiW)
      (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
        (fun t : ℝ ↦ -t) W)
  apply hi.congr
  apply MeasureTheory.ae_of_all
  intro t
  dsimp only [F]
  rw [tsum_mul_right]
  change LSeries f _ * _ = _
  rw [AnalyticNumberTheory.DirichletLFunction.LSeries_mangoldt_eq_neg_logDeriv χ
      (show (1 : ℝ) < ((((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))).re
        by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
        norm_num only)]
  dsimp only [W]
  simp only [logDeriv, Pi.div_apply, neg_div]

/-- The reflected completed-minus-ordinary logarithmic derivative integral.
This isolates the archimedean term on the inverse scale. -/
noncomputable def quarterMainArch644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      (logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) -
          logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t)) *
        (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- On the reflected line, the completed-minus-ordinary logarithmic derivative
is exactly the Gamma-factor logarithmic derivative. Nonvanishing in the right
half-plane justifies this identity inside the integral. -/
theorem quarter_arch_eq_gamma_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (x : ℝ) :
    quarterMainArch644 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  unfold quarterMainArch644
  apply congrArg (fun y : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * y)
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  let z : ℂ := (((17 / 16 : ℝ) : ℂ) - Complex.I * t)
  have hr : 1 ≤ z.re := by
    simp only [z, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
    norm_num only
  have hp : 0 < z.re := zero_lt_one.trans_le hr
  have he :=
    AnalyticNumberTheory.DirichletLFunction.L_logDeriv_sub_gamma_of_regular hne
      (AnalyticNumberTheory.DirichletLFunction.completed_ne_zero_of_one_le_re hne hr)
      (AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hp)
      (AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ
          hp).differentiableAt
  change (logDeriv χ.completedLFunction z - logDeriv χ.LFunction z) * _ = _
  rw [he]
  ring

/-- The reflected archimedean integral is the same for any two even
nonprincipal characters. Their Gamma factors are the same real Gamma factor. -/
theorem quarter_arch_even_eq_644 {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a ≠ 1) (hb : b ≠ 1) (hea : a.Even) (heb : b.Even) (x : ℝ) :
    quarterMainArch644 a x = quarterMainArch644 b x := by
  rw [quarter_arch_eq_gamma_644 a ha x, quarter_arch_eq_gamma_644 b hb x]
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- Split the primitive completed left contour into the exact conductor term,
the inverse character's ordinary Euler integral, and its archimedean remainder. -/
theorem quarter_left_euler_split_644 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        quarterMainArch644 χ⁻¹ x := by
  let K := quarterKernel644
  let W := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * W t
  let C := fun t : ℝ ↦ Complex.log q * W t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16)
      (x := x)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hC :=
    LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line K (c := -9 / 16) (x := x)
      (F := fun _ : ℝ ↦ Complex.log q) (A := ‖Complex.log q‖)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) hx MeasureTheory.aestronglyMeasurable_const
      (fun t ↦ by
        have hlog : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
        nlinarith only [hlog, norm_nonneg (Complex.log (q : ℂ))])
  simp only [mul_assoc] at hC
  change MeasureTheory.Integrable F at hF
  change MeasureTheory.Integrable C at hC
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R, W, K]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  have hO :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t) := by
    apply (quarter_ordinary_integrable_644 χ⁻¹ hx).neg.congr
    apply MeasureTheory.ae_of_all
    intro t
    simp only [Pi.neg_apply, neg_mul, neg_neg, Complex.ofReal_neg, mul_neg, sub_eq_add_neg, W, K]
  rw [quarter_main_reflection_644 hp hne hinv hx]
  dsimp only [quarterMainArch644]
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hR hO]
  ring

/-- The real ordinary term in the reflected completed contour is the negative
of the reflected Euler integral used in the three-character comparison. -/
theorem quarter_ordinary_re_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re =
      -quarterMainEuler644 χ x := by
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = (((17 / 16 : ℝ) : ℂ) - Complex.I * t) := by
    push_cast
    ring
  unfold quarterMainEuler644
  simp only [he, neg_mul, MeasureTheory.integral_neg, mul_neg, Complex.neg_re, neg_neg]

/-- The right-line Gamma integral in the refined contour remainder. -/
noncomputable def quarterRightGamma644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        (quarterKernel644.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- For a primitive nonprincipal self-inverse character, the real main
contour has the conductor and the two Gamma terms minus the reflected Euler sum. -/
theorem quarter_main_arch_split_644 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) {x : ℝ} (hx : 0 < x) :
    (contourRemainder644 χ x).re =
      Real.log q * Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ -
          quarterMainEuler644 χ x +
        (quarterMainArch644 χ x + quarterRightGamma644 χ x).re := by
  rw [contour_no_residue_644, quarter_left_euler_split_644 hp hn (inv_ne_one.mpr hn) hx, hi]
  simp only [quarterRightGamma644, Complex.add_re, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg q), ← Complex.ofReal_mul, Complex.ofReal_re,
    sub_eq_add_neg, add_assoc]
  simpa only [quarterRightGamma644, sub_eq_add_neg, add_assoc] using
    congrArg
      (fun t : ℝ ↦
        Real.log q * Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ +
          (t + ((quarterMainArch644 χ x).re + (quarterRightGamma644 χ x).re)))
      (quarter_ordinary_re_644 χ x)

/-- The sum of the two main Gamma integrals for the level-one factor.
The left line uses the reflected argument, and the right line uses the
direct argument. This common term is used in shifted even-character sums. -/
noncomputable def quarterLevelGamma644 (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
    quarterRightGamma644 (1 : DirichletCharacter ℂ 1) x

/-- For an even nonprincipal character, the two main Gamma integrals
are precisely the level-one Gamma contribution. -/
theorem quarter_even_level_gamma_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) (x : ℝ) :
    quarterMainArch644 χ x + quarterRightGamma644 χ x = quarterLevelGamma644 x := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  rw [quarter_arch_eq_gamma_644 χ hn x]
  unfold quarterLevelGamma644 quarterRightGamma644
  rw [hg]

/-- For even characters, the sum of the two Gamma contour integrals is
independent of the modulus. This combines parity invariance under inversion with
the common even Gamma factor on both vertical lines. -/
theorem quarter_even_gamma_eq_644 {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a⁻¹ ≠ 1) (hb : b⁻¹ ≠ 1) (hea : a.Even) (heb : b.Even)
    (x : ℝ) :
    quarterMainArch644 a⁻¹ x + quarterRightGamma644 a x =
      quarterMainArch644 b⁻¹ x + quarterRightGamma644 b x := by
  have heA : a⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr hea
  have heB : b⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr heb
  rw [quarter_arch_even_eq_644 a⁻¹ b⁻¹ ha hb heA heB x]
  unfold quarterRightGamma644
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- The 48-term trapezoid estimate bounds digamma at the lower reflected
argument of the section 122 gamma kernel. -/
private theorem gamma_point_left_644 : digammaReal (143 / 200) ≤ -1.178 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck (9743 / 200) 5 32 0 (3885988 / 1000000) = true from
          by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have h :=
    (AnalyticNumberTheory.Gamma.real_digamma_finite_prefix_bounds (r := (143 / 200 : ℝ))
        (by norm_num only) 48).2
  norm_num only [digammaReal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h ⊢
  linarith only [h, hl]

/-- The same trapezoid estimate at the forward gamma argument. -/
private theorem gamma_point_right_644 : digammaReal (157 / 200) ≤ -0.9998 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck (9757 / 200) 5 32 0 (3887424 / 1000000) = true from
          by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have h :=
    (AnalyticNumberTheory.Gamma.real_digamma_finite_prefix_bounds (r := (157 / 200 : ℝ))
        (by norm_num only) 48).2
  norm_num only [digammaReal, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h ⊢
  linarith only [h, hl]

/-- The zero-order coefficient of the two gamma integrals is at most
minus 2.23. The two finite digamma estimates give the bound directly. -/
theorem quarter_gamma_baseline_644 :
    (digammaReal (143 / 200) + digammaReal (157 / 200)) / 2 - Real.log Real.pi ≤ -2.23 := by
  linarith only [gamma_point_left_644, gamma_point_right_644, Analysis.log_pi_ge_2096_div_1831]

/-- For logarithmic argument at least 14, the three prescribed odd-order
coefficient bounds raise the zero-order gamma bound by less than 0.05. -/
theorem quarter_gamma_poly_upper_644 {z g₁ g₃ g₅ : ℝ} (hz : 14 ≤ z) (h₁ : |g₁| ≤ 0.131)
    (h₃ : |g₃| ≤ 0.67) (h₅ : |g₅| ≤ 10) :
    (digammaReal (143 / 200) + digammaReal (157 / 200)) / 2 - Real.log Real.pi + 5 * g₁ / z +
        10 * g₃ / z ^ 3 +
        g₅ / z ^ 5 ≤
      -2.18 := by
  have hb (k : ℕ) {a b : ℝ} (hab : a ≤ b) (h₀ : 0 ≤ b) : a / z ^ k ≤ b / 14 ^ k := by
    have hp := pow_pos (by linarith only [hz] : 0 < z) k
    exact
      (div_le_div_of_nonneg_right hab hp.le).trans
        (div_le_div_of_nonneg_left h₀ (pow_pos (by norm_num only) k)
          (pow_le_pow_left₀ (by norm_num only) hz k))
  have ha :=
    hb 1 (mul_le_mul_of_nonneg_left ((le_abs_self g₁).trans h₁) (by norm_num only : (0 : ℝ) ≤ 5))
      (by norm_num only)
  have hc :=
    hb 3 (mul_le_mul_of_nonneg_left ((le_abs_self g₃).trans h₃) (by norm_num only : (0 : ℝ) ≤ 10))
      (by norm_num only)
  have hd := hb 5 ((le_abs_self g₅).trans h₅) (by norm_num only)
  norm_num only [pow_one] at ha
  linarith only [quarter_gamma_baseline_644, ha, hc, hd]

/-- The rational majorants for the odd derivatives in (122.18) imply
the three constants used in the normalized gamma polynomial. -/
theorem quarter_gamma_odd_caps_644 {g : ℕ → ℝ}
    (hg :
      ∀ j ∈ ({1, 3, 5} : Finset ℕ),
        |g j| ≤
          (7 / 100 : ℝ) / 2 ^ (j + 1) *
            (((j + 1).factorial : ℝ) / (143 / 200) ^ (j + 2) +
              (j.factorial : ℝ) / (143 / 200) ^ (j + 1))) :
    |g 1| ≤ 0.131 ∧ |g 3| ≤ 0.67 ∧ |g 5| ≤ 10 := by
  refine ⟨(hg 1 (by decide)).trans ?_, (hg 3 (by decide)).trans ?_, (hg 5 (by decide)).trans ?_⟩
  all_goals norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.mul_one]

/-- For `x > 0` and `k > 1`, the reciprocal-power series is bounded by
its first term plus the integral of the decreasing weight. -/
theorem quarter_reciprocal_sum_644 {x k : ℝ} (hx : 0 < x) (hk : 1 < k) :
    Summable (fun n : ℕ ↦ (x + n) ^ (-k)) ∧
      (∑' n : ℕ, (x + n) ^ (-k)) ≤ x ^ (-k) + x ^ (1 - k) / (k - 1) := by
  have hn (n : ℕ) : 0 ≤ (x + n) ^ (-k) := Real.rpow_nonneg (add_nonneg hx.le (Nat.cast_nonneg n)) _
  have hpartial (N : ℕ) :
    (∑ n ∈ Finset.range N, (x + n) ^ (-k)) ≤ x ^ (-k) + x ^ (1 - k) / (k - 1) := by
    cases N with
    | zero =>
      rw [Finset.sum_range_zero]
      positivity
    | succ N =>
      rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
      have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-k)) (Set.Icc x (x + (N : ℝ))) := fun _ hu _ _ huv ↦
        Real.rpow_le_rpow_of_nonpos (hx.trans_le hu.1) huv (by linarith only [hk])
      have h := hanti.sum_le_integral
      have hN : x ≤ x + (N : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
      have hmem : (0 : ℝ) ∉ Set.uIcc x (x + (N : ℝ)) := by
        rw [Set.uIcc_of_le hN]
        exact fun ht ↦ hx.not_ge ht.1
      rw [integral_rpow (Or.inr ⟨by linarith only [hk], hmem⟩)] at h
      have he : ((x + (N : ℝ)) ^ (-k + 1) - x ^ (-k + 1)) / (-k + 1) ≤ x ^ (1 - k) / (k - 1) := by
        rw [show -k + 1 = 1 - k by ring, show 1 - k = -(k - 1) by ring, div_neg, ← neg_div]
        apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hk.le)
        linarith only [Real.rpow_nonneg (hx.le.trans hN) (-(k - 1))]
      rw [add_comm]
      exact add_le_add (le_refl _) (h.trans he)
  have hs := summable_of_sum_range_le hn hpartial
  exact ⟨hs, hs.tsum_le_of_sum_range_le hpartial⟩

/-- The mean value theorem bounds a reciprocal-power difference by the
derivative magnitude at its positive left endpoint. -/
private theorem reciprocal_diff_le {x y k : ℝ} (hx : 0 < x) (hxy : x < y) (hk : 0 ≤ k) :
    x ^ (-k) - y ^ (-k) ≤ k * (y - x) * x ^ (-k - 1) := by
  have hd (u : ℝ) (hu : 0 < u) := Real.hasDerivAt_rpow_const (p := -k) (Or.inl hu.ne')
  obtain ⟨c, hc, he⟩ :=
    exists_deriv_eq_slope (fun u : ℝ ↦ u ^ (-k)) hxy
      (fun u hu ↦ (hd u (hx.trans_le hu.1)).continuousAt.continuousWithinAt)
      (fun u hu ↦ (hd u (hx.trans hu.1)).differentiableAt.differentiableWithinAt)
  rw [(hd c (hx.trans hc.1)).deriv] at he
  have he' := (eq_div_iff (sub_ne_zero.mpr hxy.ne')).mp he
  have hv := Real.rpow_le_rpow_of_nonpos hx hc.1.le (by linarith only [hk] : -k - 1 ≤ 0)
  have hb := mul_le_mul_of_nonneg_left hv (mul_nonneg hk (sub_nonneg.mpr hxy.le))
  nlinarith only [he', hb]

/-- The difference of two reciprocal-power sums is nonnegative and bounded
by the separation times the integral-test bound on the derivative series. -/
theorem quarter_reciprocal_diff_644 {x y k : ℝ} (hx : 0 < x) (hxy : x < y) (hk : 1 < k) :
    let D := (∑' n : ℕ, (x + n) ^ (-k)) - ∑' n : ℕ, (y + n) ^ (-k)
    0 ≤ D ∧ D ≤ k * (y - x) * (x ^ (-(k + 1)) + x ^ (-k) / k) := by
  intro D
  have hsx := (quarter_reciprocal_sum_644 hx hk).1
  have hsy := (quarter_reciprocal_sum_644 (hx.trans hxy) hk).1
  have hu := quarter_reciprocal_sum_644 hx (show 1 < k + 1 by linarith only [hk])
  have hg : 0 ≤ k * (y - x) := mul_nonneg (by linarith only [hk]) (sub_nonneg.mpr hxy.le)
  have hp (n : ℕ) : (x + n) ^ (-k) - (y + n) ^ (-k) ≤ k * (y - x) * (x + n) ^ (-(k + 1)) := by
    have h :=
      reciprocal_diff_le (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n))
        (add_lt_add_of_lt_of_le hxy (le_refl (n : ℝ))) (show 0 ≤ k by linarith only [hk])
    rwa [add_sub_add_right_eq_sub, show -k - 1 = -(k + 1) by ring] at h
  have hb := (hsx.sub hsy).tsum_le_tsum hp (hu.1.mul_left (k * (y - x)))
  rw [hsx.tsum_sub hsy, tsum_mul_left] at hb
  have he := hu.2
  rw [show 1 - (k + 1) = -k by ring, show k + 1 - 1 = k by ring] at he
  exact
    ⟨sub_nonneg.mpr
        (hsy.tsum_le_tsum
          (fun n ↦
            Real.rpow_le_rpow_of_nonpos (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n))
              (add_le_add hxy.le le_rfl) (by linarith only [hk]))
          hsx),
      hb.trans (mul_le_mul_of_nonneg_left he hg)⟩

/-- The odd-order digamma coefficient is a factorial multiple of the
difference of reciprocal-power series at the two gamma arguments. -/
noncomputable def quarterGammaOdd644 (j : ℕ) : ℝ :=
  (j.factorial : ℝ) / 2 ^ (j + 1) *
    ((∑' n : ℕ, (143 / 200 + n : ℝ) ^ (-((j : ℝ) + 1))) -
      ∑' n : ℕ, (157 / 200 + n : ℝ) ^ (-((j : ℝ) + 1)))

/-- The reciprocal-series coefficients of orders one, three and five
obey the rational caps in the section 122 gamma polynomial. -/
theorem quarter_gamma_odd_series_644 :
    |quarterGammaOdd644 1| ≤ 0.131 ∧
      |quarterGammaOdd644 3| ≤ 0.67 ∧ |quarterGammaOdd644 5| ≤ 10 := by
  apply quarter_gamma_odd_caps_644
  intro j hj
  have hj₀ : 0 < j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> decide
  have hj₁ : 1 < (j : ℝ) + 1 := by linarith only [(show (0 : ℝ) < j from Nat.cast_pos.mpr hj₀)]
  have h :=
    quarter_reciprocal_diff_644 (x := 143 / 200) (y := 157 / 200) (by norm_num only)
      (by norm_num only) hj₁
  dsimp only at h
  unfold quarterGammaOdd644
  rw [abs_of_nonneg (mul_nonneg (by positivity) h.1)]
  refine (mul_le_mul_of_nonneg_left h.2 (by positivity)).trans (le_of_eq ?_)
  rw [show (157 / 200 : ℝ) - 143 / 200 = 7 / 100 by norm_num only, ← Nat.cast_succ, ← Nat.cast_succ,
    Real.rpow_neg (by norm_num only), Real.rpow_neg (by norm_num only), Real.rpow_natCast,
    Real.rpow_natCast, Nat.factorial_succ, Nat.cast_mul]
  field_simp [show ((j + 1 : ℕ) : ℝ) ≠ 0 by positivity]

/-- The certified reciprocal-series coefficients give the section 122
polynomial upper bound whenever the logarithmic argument is at least 14. -/
theorem quarter_gamma_series_upper_644 {z : ℝ} (hz : 14 ≤ z) :
    (digammaReal (143 / 200) + digammaReal (157 / 200)) / 2 - Real.log Real.pi +
        5 * quarterGammaOdd644 1 / z +
        10 * quarterGammaOdd644 3 / z ^ 3 +
        quarterGammaOdd644 5 / z ^ 5 ≤
      -2.18 := by
  obtain ⟨h₁, h₃, h₅⟩ := quarter_gamma_odd_series_644
  exact quarter_gamma_poly_upper_644 hz h₁ h₃ h₅

/-- The first gamma pole contribution at logarithmic coordinate `z`.
It integrates the truncated sixth-pole weight with decay rate 57/100. -/
noncomputable def quarterGammaFirst644 (z : ℝ) : ℝ :=
  ((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2) * z) *
    ∫ t in (0 : ℝ)..z, Real.exp (-(57 / 100) * t) * t ^ 5

/-- The first gamma pole contribution is nonnegative on its support. -/
theorem quarter_gamma_first_nonneg_644 {z : ℝ} (hz : 0 ≤ z) : 0 ≤ quarterGammaFirst644 z := by
  unfold quarterGammaFirst644
  exact
    mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hz fun t ht ↦
        mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.1 _))

/-- Differentiating the first gamma pole contribution yields the endpoint
weight minus one half of the same contribution. -/
theorem quarter_gamma_first_deriv_644 (z : ℝ) :
    HasDerivAt quarterGammaFirst644
      ((107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5 - quarterGammaFirst644 z / 2)
      z := by
  let f := fun t : ℝ ↦ Real.exp (-(57 / 100) * t) * t ^ 5
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (continuous_id.pow 5)
  have hi :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 z)
      hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have he :=
    (((hasDerivAt_id z).const_mul (-(1 / 2) : ℝ)).exp.const_mul ((107 / 100 : ℝ) ^ 5 / 120)).mul hi
  unfold quarterGammaFirst644
  convert he using 1
  · rfl
  · dsimp only [f, id_eq]
    have h :
      Real.exp (-(107 / 100) * z) = Real.exp (-(1 / 2) * z) * Real.exp (-(57 / 100) * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h]
    ring

/-- In radius coordinates `z = 2.687 + 2 log r`, the derivative of the
first gamma pole times `r` is twice the endpoint weight minus the pole term. -/
theorem quarter_gamma_first_radius_644 {r : ℝ} (hr : 0 < r) :
    let z := 2687 / 1000 + 2 * Real.log r
    r * deriv (fun u ↦ quarterGammaFirst644 (2687 / 1000 + 2 * Real.log u)) r =
      2 * ((107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5) -
        quarterGammaFirst644 z := by
  intro z
  have hz := ((Real.hasDerivAt_log hr.ne').const_mul 2).const_add (2687 / 1000)
  have hd := ((quarter_gamma_first_deriv_644 z).comp r hz).deriv
  simp only [Function.comp_def] at hd
  rw [hd]
  have h : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  linear_combination
    (2 * ((107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5) -
        quarterGammaFirst644 z) *
      h

/-- The first gamma pole is a difference of two exponential moment
endpoint values. This formula allows rational endpoint certification. -/
theorem quarter_gamma_first_closed_644 {z : ℝ} (hz : 0 ≤ z) :
    quarterGammaFirst644 z =
      ((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2) * z) *
        (Analysis.logPowerTailPoly (57 / 100) 5 0 -
          Real.exp (-(57 / 100) * z) * Analysis.logPowerTailPoly (57 / 100) 5 z) := by
  unfold quarterGammaFirst644
  rw [intervalIntegral.integral_of_le hz]
  simp_rw [mul_comm (Real.exp _)]
  rw [Analysis.exponential_moment_interval_ne (by norm_num only) hz 5]
  rw [mul_comm (Analysis.logPowerTailPoly (57 / 100) 5 z)]

/-- The truncated first-pole integral dominates `z / 6` times its
endpoint weight because the exponential is decreasing. -/
theorem quarter_gamma_first_ratio_644 {z : ℝ} (hz : 0 ≤ z) :
    z / 6 * ((107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5) ≤
      quarterGammaFirst644 z := by
  let d : ℝ := 57 / 100
  let f := fun t : ℝ ↦ Real.exp (-d * t) * t ^ 5
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (continuous_id.pow 5)
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hz
      (((continuous_id.pow 5).const_mul (Real.exp (-d * z))).intervalIntegrable 0 z)
      (hf.intervalIntegrable 0 z)
      (fun t ht ↦
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 (by norm_num only [d])))
          (pow_nonneg ht.1 _))
  rw [intervalIntegral.integral_const_mul] at hi
  change Real.exp (-d * z) * (∫ t in (0 : ℝ)..z, t ^ 5) ≤ _ at hi
  rw [integral_pow] at hi
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow, OfNat.ofNat_ne_zero, sub_zero] at hi
  have he : Real.exp (-(107 / 100) * z) = Real.exp (-(1 / 2) * z) * Real.exp (-d * z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [d]
    ring
  unfold quarterGammaFirst644
  rw [he]
  calc
    _ = ((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2) * z) * (Real.exp (-d * z) * (z ^ 6 / 6)) :=
      by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)

/-- The first gamma pole decreases above logarithmic coordinate fourteen.
Its right endpoint therefore gives a lower bound on every such interval. -/
theorem quarter_gamma_first_antitone_644 : AntitoneOn quarterGammaFirst644 (Set.Ici (14 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact
      (continuous_iff_continuousAt.mpr
          (fun z ↦ (quarter_gamma_first_deriv_644 z).continuousAt)).continuousOn
  · exact fun z _ ↦ (quarter_gamma_first_deriv_644 z).differentiableAt.differentiableWithinAt
  · intro z hz
    have h14 : 14 ≤ z := interior_subset hz
    have h := quarter_gamma_first_ratio_644 (by linarith only [h14] : 0 ≤ z)
    have hp : 0 ≤ (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5 := by
      have hz₀ : 0 ≤ z := by linarith only [h14]
      positivity
    rw [(quarter_gamma_first_deriv_644 z).deriv]
    nlinarith only [h, mul_nonneg (show 0 ≤ z / 6 - 2 by linarith only [h14]) hp]

/-- An upper bound for the outer exponential and a lower bound for the
inner exponential turn the closed first-pole formula into a rational lower bound. -/
private theorem gamma_first_box {z l u m : ℝ} (hz : 0 ≤ z) (hl : 0 < l) (hu : 0 < u)
    (he₁ : l ≤ Real.exp ((57 / 100) * z)) (he₂ : Real.exp ((1 / 2) * z) ≤ u)
    (hp : 0 ≤ Analysis.logPowerTailPoly (57 / 100) 5 z)
    (hd :
      0 ≤ Analysis.logPowerTailPoly (57 / 100) 5 0 - Analysis.logPowerTailPoly (57 / 100) 5 z / l)
    (hm :
      m ≤
        (107 / 100 : ℝ) ^ 5 / 120 * (1 / u) *
          (Analysis.logPowerTailPoly (57 / 100) 5 0 -
            Analysis.logPowerTailPoly (57 / 100) 5 z / l)) :
    m ≤ quarterGammaFirst644 z := by
  rw [quarter_gamma_first_closed_644 hz, neg_mul, Real.exp_neg, neg_mul, Real.exp_neg]
  have h₁ := inv_le_inv₀ (Real.exp_pos ((57 / 100) * z)) hl |>.2 he₁
  have h₂ := inv_le_inv₀ hu (Real.exp_pos ((1 / 2) * z)) |>.2 he₂
  rw [one_div] at hm
  have hp' :
    Analysis.logPowerTailPoly (57 / 100) 5 z / l = l⁻¹ * Analysis.logPowerTailPoly (57 / 100) 5 z :=
    div_eq_inv_mul _ _
  rw [hp'] at hm hd
  have he :=
    sub_le_sub_left (mul_le_mul_of_nonneg_right h₁ hp) (Analysis.logPowerTailPoly (57 / 100) 5 0)
  have hfactor := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ (107 / 100 : ℝ) ^ 5 / 120 by norm_num only)
  exact hm.trans (mul_le_mul hfactor he hd (by positivity))

/-- The first gamma pole at logarithmic cut 14.237 exceeds 0.02712. -/
theorem quarter_gamma_first_14237 : 0.02712 ≤ quarterGammaFirst644 (14237 / 1000) := by
  have h₁ :=
    shift122_exp_box (x := (57 / 100) * (14237 / 1000)) (l := 3344) (u := 3345) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have h₂ :=
    shift122_exp_box (x := (1 / 2) * (14237 / 1000)) (l := 1234) (u := 1235) (by norm_num only)
      (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  refine gamma_first_box (by norm_num only) (by norm_num only) (by norm_num only) h₁.1 h₂.2 ?_ ?_ ?_
  all_goals norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one]

/-- The last logarithmic endpoint gives a common first-pole lower bound
for all four section 122 radius intervals. -/
theorem quarter_gamma_first_rows_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    0.02712 ≤ quarterGammaFirst644 (2687 / 1000 + 2 * Real.log r) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 9) (n := 27) (lo := 5755 / 1000)
        (hi := 5756 / 1000) (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo := 5774 / 1000)
        (hi := 5775 / 1000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h₁ h₂
  have hl := h₁.trans (Real.log_le_log (by norm_num only) hr.1)
  have hu := (Real.log_le_log (by linarith only [hr.1]) hr.2).trans h₂
  exact
    quarter_gamma_first_14237.trans
      (quarter_gamma_first_antitone_644
        (show (14 : ℝ) ≤ 2687 / 1000 + 2 * Real.log r by linarith only [hl])
        (show (14 : ℝ) ≤ 14237 / 1000 by norm_num only) (by linarith only [hu]))

end PseudoPrime.PrimeTestBounds.MillerRabin
