/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainEuler656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterForward656
import all PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDualReflection

/-! # Completed contour and common even Gamma term of the section 132 kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale, primitivity and nonprincipality give integrability of
the reflected completed logarithmic derivative against the main kernel. -/
private theorem reflected_completed_integrable_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := quarterKernel656
  let w := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * w t
  let C := fun t : ℝ ↦ Complex.log q * w t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * w t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16)
      (x := x)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hC : MeasureTheory.Integrable C := (line_integrable hx).const_mul (Complex.log q)
  change MeasureTheory.Integrable F at hF
  change MeasureTheory.Integrable C at hC
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  exact hR

/-- Reflect the completed left contour and identify the exact inverse-scale
conductor term. -/
theorem quarter_main_reflection_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := quarterKernel656
  let w := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * w t
  let C := fun t : ℝ ↦ Complex.log q * w t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * w t
  have hC : MeasureTheory.Integrable C := (line_integrable hx).const_mul (Complex.log q)
  have hR : MeasureTheory.Integrable R := reflected_completed_integrable_656 hp hne hinv hx
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hi : (∫ t : ℝ, F t) = (∫ t : ℝ, C t) + ∫ t : ℝ, R t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
      MeasureTheory.integral_add hC hR]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hi, mul_add]
  have hcint :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, C t) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ : ℂ) := by
    dsimp only [C, w, K]
    rw [MeasureTheory.integral_const_mul]
    rw [← mul_assoc, mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)) (Complex.log q), mul_assoc,
      quarter_left_kernel_656 hx]
  rw [hcint]

/-- The main contour remainder splits into the inverse-scale conductor,
reflected completed logarithmic derivative and forward gamma integral. -/
theorem quarter_main_contour_reflect_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let W := fun z : ℂ ↦ quarterKernel656.function z * (x : ℂ) ^ z
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    contourRemainder656 χ x =
      Complex.log q * (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ : ℂ) +
        d * (∫ t : ℝ, logDeriv χ⁻¹.completedLFunction (w t) * W (l t)) +
        d * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)) := by
  dsimp only
  rw [contour_no_residue_656, quarter_main_reflection_656 hp hn (inv_ne_one.mpr hn) hx]

/-- The ordinary reflected logarithmic derivative against the sixth-pole
left-line weight is integrable at every positive scale. Sum the integrable
Dirichlet terms using the absolute integrated-norm bound. -/
theorem quarter_ordinary_integrable_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let W := fun t : ℝ ↦
    quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hiW : MeasureTheory.Integrable W := line_integrable hx
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
noncomputable def quarterMainArch656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      (logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) -
          logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t)) *
        (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- On the reflected line, the completed-minus-ordinary logarithmic derivative
is exactly the Gamma-factor logarithmic derivative. Nonvanishing in the right
half-plane justifies this identity inside the integral. -/
theorem quarter_arch_eq_gamma_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (x : ℝ) :
    quarterMainArch656 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  unfold quarterMainArch656
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
theorem quarter_arch_even_eq_656 {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a ≠ 1) (hb : b ≠ 1) (hea : a.Even) (heb : b.Even) (x : ℝ) :
    quarterMainArch656 a x = quarterMainArch656 b x := by
  rw [quarter_arch_eq_gamma_656 a ha x, quarter_arch_eq_gamma_656 b hb x]
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- Split the primitive completed left contour into the exact conductor term,
the inverse character's ordinary Euler integral, and its archimedean remainder. -/
theorem quarter_left_euler_split_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        quarterMainArch656 χ⁻¹ x := by
  let K := quarterKernel656
  let W := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t
  have hR : MeasureTheory.Integrable R := reflected_completed_integrable_656 hp hne hinv hx
  have hO :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t) := by
    apply (quarter_ordinary_integrable_656 χ⁻¹ hx).neg.congr
    apply MeasureTheory.ae_of_all
    intro t
    simp only [Pi.neg_apply, neg_mul, neg_neg, Complex.ofReal_neg, mul_neg, sub_eq_add_neg, W, K]
  rw [quarter_main_reflection_656 hp hne hinv hx]
  dsimp only [quarterMainArch656]
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hR hO]
  ring

/-- The real ordinary term in the reflected completed contour is the negative
of the reflected Euler integral used in the three-character comparison. -/
theorem quarter_ordinary_re_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re =
      -quarterMainEuler656 χ x := by
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = (((17 / 16 : ℝ) : ℂ) - Complex.I * t) := by
    push_cast
    ring
  unfold quarterMainEuler656
  simp only [he, neg_mul, MeasureTheory.integral_neg, mul_neg, Complex.neg_re, neg_neg]

/-- The right-line Gamma integral in the refined contour remainder. -/
noncomputable def quarterRightGamma656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        (quarterKernel656.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- For a primitive nonprincipal self-inverse character, the real main
contour has the conductor and the two Gamma terms minus the reflected Euler sum. -/
theorem quarter_main_arch_split_656 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) {x : ℝ} (hx : 0 < x) :
    (contourRemainder656 χ x).re =
      Real.log q * Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ - quarterMainEuler656 χ x +
        (quarterMainArch656 χ x + quarterRightGamma656 χ x).re := by
  rw [contour_no_residue_656, quarter_left_euler_split_656 hp hn (inv_ne_one.mpr hn) hx, hi]
  simp only [quarterRightGamma656, Complex.add_re, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg q), ← Complex.ofReal_mul, Complex.ofReal_re,
    sub_eq_add_neg, add_assoc]
  simpa only [quarterRightGamma656, sub_eq_add_neg, add_assoc] using
    congrArg
      (fun t : ℝ ↦
        Real.log q * Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ +
          (t + ((quarterMainArch656 χ x).re + (quarterRightGamma656 χ x).re)))
      (quarter_ordinary_re_656 χ x)

/-- The sum of the two main Gamma integrals for the level-one factor.
The left line uses the reflected argument, and the right line uses the
direct argument. This common term is used in shifted even-character sums. -/
noncomputable def quarterLevelGamma656 (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
    quarterRightGamma656 (1 : DirichletCharacter ℂ 1) x

/-- For an even nonprincipal character, the two main Gamma integrals
are precisely the level-one Gamma contribution. -/
theorem quarter_even_level_gamma_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (he : χ.Even) (x : ℝ) :
    quarterMainArch656 χ x + quarterRightGamma656 χ x = quarterLevelGamma656 x := by
  have hg : χ.gammaFactor = (1 : DirichletCharacter ℂ 1).gammaFactor := by
    funext z
    rw [he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  rw [quarter_arch_eq_gamma_656 χ hn x]
  unfold quarterLevelGamma656 quarterRightGamma656
  rw [hg]

/-- For even characters, the sum of the two Gamma contour integrals is
independent of the modulus. This combines parity invariance under inversion with
the common even Gamma factor on both vertical lines. -/
theorem quarter_even_gamma_eq_656 {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a⁻¹ ≠ 1) (hb : b⁻¹ ≠ 1) (hea : a.Even) (heb : b.Even)
    (x : ℝ) :
    quarterMainArch656 a⁻¹ x + quarterRightGamma656 a x =
      quarterMainArch656 b⁻¹ x + quarterRightGamma656 b x := by
  have heA : a⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr hea
  have heB : b⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr heb
  rw [quarter_arch_even_eq_656 a⁻¹ b⁻¹ ha hb heA heB x]
  unfold quarterRightGamma656
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

end PseudoPrime.PrimeTestBounds.MillerRabin
