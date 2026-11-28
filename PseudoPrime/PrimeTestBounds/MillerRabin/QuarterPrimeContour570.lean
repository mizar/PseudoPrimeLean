/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLeftContour570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGamma570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriple570
public import PseudoPrime.LLS.PaperStatements.MellinKernelExplicitFormula

/-! # The explicit formula for the section 31 prime sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The ordinary reflected logarithmic derivative against the sixth-pole
left-line weight is integrable at every positive scale. Sum the integrable
Dirichlet terms using the absolute integrated-norm bound. -/
theorem reflected_ordinary_integrable_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let W := fun t : ℝ ↦
    quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hiW : MeasureTheory.Integrable W := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip quarterKernel570 (c :=
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
noncomputable def reflectedArch570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      (logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) -
          logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t)) *
        (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- On the reflected line, the completed-minus-ordinary logarithmic derivative
is exactly the Gamma-factor logarithmic derivative. Nonvanishing in the right
half-plane justifies this identity inside the integral. -/
theorem reflected_arch_eq_gamma_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (x : ℝ) :
    reflectedArch570 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  unfold reflectedArch570
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
theorem reflected_arch_even_eq_570 {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a ≠ 1) (hb : b ≠ 1) (hea : a.Even) (heb : b.Even) (x : ℝ) :
    reflectedArch570 a x = reflectedArch570 b x := by
  rw [reflected_arch_eq_gamma_570 a ha x, reflected_arch_eq_gamma_570 b hb x]
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- Split the primitive completed left contour into the exact conductor term,
the inverse character's ordinary Euler integral, and its archimedean remainder. -/
theorem left_euler_split_570 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        reflectedArch570 χ⁻¹ x := by
  let K := quarterKernel570
  let W := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * W t
  let C := fun t : ℝ ↦ Complex.log q * W t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * W t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
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
    apply (reflected_ordinary_integrable_570 χ⁻¹ hx).neg.congr
    apply MeasureTheory.ae_of_all
    intro t
    simp only [Pi.neg_apply, neg_mul, neg_neg, Complex.ofReal_neg, mul_neg, sub_eq_add_neg, W, K]
  rw [left_reflection_570 hp hne hinv hx]
  dsimp only [reflectedArch570]
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hR hO]
  ring

/-- The real ordinary term in the reflected completed contour is the negative
of the reflected Euler integral used in the three-character comparison. -/
theorem ordinary_re_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re =
      -reflectedIntegral570 χ x := by
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = (((17 / 16 : ℝ) : ℂ) - Complex.I * t) := by
    push_cast
    ring
  unfold reflectedIntegral570
  simp only [he, neg_mul, MeasureTheory.integral_neg, mul_neg, Complex.neg_re, neg_neg]

/-- The right-line Gamma integral in the refined contour remainder. -/
noncomputable def rightGamma570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
        (quarterKernel570.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))

/-- For even characters, the sum of the two Gamma contour integrals is
independent of the modulus. This combines parity invariance under inversion with
the common even Gamma factor on both vertical lines. -/
theorem even_gamma_cost_eq_570 {p q : ℕ} [NeZero p] [NeZero q] (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (ha : a⁻¹ ≠ 1) (hb : b⁻¹ ≠ 1) (hea : a.Even) (heb : b.Even)
    (x : ℝ) :
    reflectedArch570 a⁻¹ x + rightGamma570 a x = reflectedArch570 b⁻¹ x + rightGamma570 b x := by
  have heA : a⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr hea
  have heB : b⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr heb
  rw [reflected_arch_even_eq_570 a⁻¹ b⁻¹ ha hb heA heB x]
  unfold rightGamma570
  have hγ : a.gammaFactor = b.gammaFactor := by
    funext z
    rw [hea.gammaFactor_def, heb.gammaFactor_def]
  rw [hγ]

/-- The conductor and Gamma terms remaining after the reflected Euler term is
separated from the refined contour remainder. -/
noncomputable def contourNonEuler570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ : ℂ)).re +
    (reflectedArch570 χ⁻¹ x).re +
    (rightGamma570 χ x).re

/-- The pole residue and the two contour integrals on the fixed lines ±9/16. -/
noncomputable def contourRemainder570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let W := fun s : ℂ ↦ quarterKernel570.function s * (x : ℂ) ^ s
  LLS.PaperStatements.MellinKernel.weightedResidue quarterKernel570
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          W (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) +
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          W (((9 / 16 : ℝ) : ℂ) + Complex.I * t))

/-- Under GRH, the refined arithmetic sum equals the contour remainder minus its zero sum. -/
theorem contour_formula_570 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, quarterKernel570.summand χ x n) =
      contourRemainder570 χ x - ∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ x ρ := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_summand_eq_completed_residue_formula quarterKernel570 hq
      hGRH hp hne hinv (a := (-9 / 16 : ℝ)) (b := 9 / 16) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only [contourRemainder570] at *
  linear_combination h

/-- The refined kernel has no residue at the regularization point minus one half. -/
theorem pole_residue_zero_570 (F : ℂ → ℂ) (x : ℝ) :
    LLS.PaperStatements.MellinKernel.weightedResidue quarterKernel570 F x (-1 / 2) = 0 := by
  simp only [LLS.PaperStatements.MellinKernel.weightedResidue]
  change
    -logDeriv F (-1 / 2) *
        (((-1 / 2 : ℂ) + 1 / 2) * quarterKernel570.function (-1 / 2) * (x : ℂ) ^ (-1 / 2)) =
      0
  rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]

/-- The refined contour remainder consists exactly of its two vertical integrals. -/
theorem contour_no_residue_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    contourRemainder570 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (quarterKernel570.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  simp only [contourRemainder570, pole_residue_zero_570, zero_add]

/-- For a nonprincipal character, the zero-term norm is its nonnegative multiplicity
times the kernel norm. -/
theorem kernel_zero_norm_570 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (ρ : ℂ) :
    ‖quarterKernel570.kernelZeroTerm χ ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖quarterKernel570.function (Complex.I * ρ.im)‖ := by
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  unfold LLS.PaperStatements.MellinKernel.kernelZeroTerm
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hd]

/-- Under GRH, the oscillatory zero sum is bounded in norm by the actual refined zero mass. -/
theorem oscillating_zero_le_mass_570 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, quarterKernel570.oscillatingZeroTerm χ x ρ‖ ≤ quarterMass570 χ := by
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm quarterKernel570 hq hGRH hp hne
      hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm quarterKernel570 χ hx ρ).trans
      (kernel_zero_norm_570 hne ρ)
  rw [tsum_congr he] at hn
  exact hn

/-- For a primitive nonprincipal character under GRH, the real prime sum is bounded
by the conductor and gamma costs minus the inverse reflected Euler integral plus zero mass. -/
theorem contour_prime_upper_570 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, quarterKernel570.summand χ x n).re ≤
      contourNonEuler570 χ x - reflectedIntegral570 χ⁻¹ x + quarterMass570 χ := by
  have hx0 := zero_lt_one.trans_le hx
  have he := congrArg Complex.re (contour_formula_570 hq hGRH hp hne hinv hx)
  rw [contour_no_residue_570, left_euler_split_570 hp hne hinv hx0] at he
  simp only [Complex.add_re, Complex.sub_re, ordinary_re_570] at he
  have hm := oscillating_zero_le_mass_570 hq hGRH hp hne hinv hx0
  have hr := (Complex.abs_re_le_norm _).trans hm
  unfold contourNonEuler570 rightGamma570
  linarith only [he, (abs_le.mp hr).1]

/-- Inversion preserves the real reflected Euler integral, since it conjugates each
character coefficient in the absolutely convergent real-part series. -/
theorem reflected_inv_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    reflectedIntegral570 χ⁻¹ x = reflectedIntegral570 χ x := by
  rw [← (reflected_hasSum_570 χ⁻¹ hx).tsum_eq, ← (reflected_hasSum_570 χ hx).tsum_eq]
  apply tsum_congr
  intro n
  rw [← MulChar.star_apply']
  rfl

/-- At radii 278 to 285 the three prime sums are bounded by their conductor and gamma
costs plus their zero masses, with a strict saving of 0.0273 from the reflected integral. -/
theorem triple_contour_upper_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hRH : RiemannHypothesis)
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s) (pa : a.IsPrimitive) (pb : b.IsPrimitive)
    (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1) (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1)
    (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let x := r ^ 2
    (∑' n : ℕ, quarterKernel570.summand a x n).re + (∑' n : ℕ, quarterKernel570.summand b x n).re +
        (∑' n : ℕ, quarterKernel570.summand c x n).re <
      contourNonEuler570 a x + contourNonEuler570 b x + contourNonEuler570 c x +
          (quarterMass570 a + quarterMass570 b + quarterMass570 c) -
        273 / 10000 := by
  intro x
  have hx : 1 ≤ x := one_le_pow₀ (show 1 ≤ r by linarith only [hl])
  have h1 := contour_prime_upper_570 hP hG pa na ia hx
  have h2 := contour_prime_upper_570 hQ hG pb nb ib hx
  have h3 := contour_prime_upper_570 hS hG pc nc ic hx
  simp only [reflected_inv_570 _ (zero_lt_one.trans_le hx)] at h1 h2 h3
  have hd := reflected_integrals_lt_570 hRH hl hu a b c ht hA hB hC
  change -(reflectedIntegral570 a x + reflectedIntegral570 b x + reflectedIntegral570 c x) < _ at hd
  linarith only [h1, h2, h3, hd]

/-- For three primitive even characters satisfying the section 31 sign and conductor bounds,
GRH bounds their prime sums throughout the radius interval from 278 to 285. Combine the
zero-mass estimate with the signed reflected Euler term and the common even Gamma integral. -/
theorem triple_explicit_upper_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) :
    let x := r ^ 2
    (∑' n : ℕ, quarterKernel570.summand a x n).re + (∑' n : ℕ, quarterKernel570.summand b x n).re +
        (∑' n : ℕ, quarterKernel570.summand c x n).re <
      4 * r * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ +
          3 * (reflectedArch570 a⁻¹ x + rightGamma570 a x).re +
          (3 / 4 * r - 13386 / 1000 + 4 * positiveTail570 x) -
        273 / 10000 := by
  intro x
  have h :=
    triple_contour_upper_570 hG hG.riemann a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB
      hC
  have hm :=
    quarter_mass_radius_570 a b c hP hQ hS (hG p a pa) (hG q b pb) (hG s c pc) pa pb pc na nb nc ia
      ib ic hl hu ht hA hB hC hlog hG.riemann ea eb ec
  have hb := congrArg Complex.re (even_gamma_cost_eq_570 b a ib ia eb ea x)
  have hc := congrArg Complex.re (even_gamma_cost_eq_570 c a ic ia ec ea x)
  have hw := (quarter_reflected_weight_570 hl hu).1
  have hr : 0 < r := by linarith only [hl]
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re, one_div] at hw
  have hp : 0 ≤ Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ := by linarith only [hw]
  have hd := mul_le_mul_of_nonneg_right hlog hp
  dsimp only at h
  unfold contourNonEuler570 at h
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _),
    ← Complex.ofReal_mul, Complex.ofReal_re] at h
  simp only [Complex.add_re] at hb hc ⊢
  linarith only [h, hm, hb, hc, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
