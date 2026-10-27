/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedConductorRemainder
public import PseudoPrime.AnalyticNumberTheory.General.WeightedDirichletIntegrals
public import PseudoPrime.Analysis.IntegralSeries

/-! # Reflected Euler integrals and the completed Gamma remainder -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For any Dirichlet character and positive scale, integrate the reflected Euler
series term by term against the actual left Gamma weight. Absolute convergence on
real part 17/16 and weight integrability justify the exchange. This supplies the
actual contour interface for negative-strip inversion. -/
theorem gamma_reflected_euler_integral_exchange {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    (∫ t : ℝ,
        LSeries ((fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
            (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          gammaSignedLeftWeight x t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          LSeries.term ((fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
              (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n *
            gammaSignedLeftWeight x t := by
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show 1 < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  exact
    AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs (fun t : ℝ ↦ -t)
      (gammaSignedLeftWeight x) continuous_neg (integrable_gammaSignedLeftWeight hx)

/-- For a nonzero natural coefficient index and positive scale, factor the reflected
Dirichlet term times the actual Gamma weight into a constant and the inverse-Mellin
weight with base nx. Positive bases remove branch ambiguities. This identifies
the individual integrals before summing them. -/
theorem reflected_euler_term_factor (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term a (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * gammaSignedLeftWeight x t =
      (a n * (((1 / ((n : ℝ) * Real.sqrt x) : ℝ) : ℂ))) *
        (Complex.Gamma (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) *
          (((n : ℝ) * x : ℝ) : ℂ) ^ (((-1 / 16 : ℝ) : ℂ) + t * Complex.I)) := by
  let z : ℂ := ((-1 / 16 : ℝ) : ℂ) + t * Complex.I
  have he : (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) = 1 - z := by
    dsimp only [z]
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [LSeries.term_of_ne_zero hn, he, Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn),
    Complex.cpow_one, gammaSignedLeftWeight_eq_factored hx]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hx.le]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]
  dsimp only [z]
  norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [div_div_eq_mul_div]
  ring

/-- For any coefficient sequence, natural index and positive scale, the normalized
individual reflected Euler integral equals its reflected real kernel times the coefficient.
Handle index zero directly and apply negative-strip Gamma inversion at positive indices.
This transfers origin-residue cancellation to the actual coefficient integrals. -/
theorem gamma_reflected_euler_term_integral (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term a (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n *
            gammaSignedLeftWeight x t)) =
      a n * (Analysis.reflectedEulerKernel x n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero,
      Analysis.reflectedEulerKernel, Nat.cast_zero, div_zero, Complex.ofReal_zero, mul_zero]
  · have he :=
      Analysis.negative_Gamma_vertical_integral_eq (c := -1 / 16) (by norm_num only)
        (by norm_num only) (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)
    have hΓ :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            Complex.Gamma (((-1 / 16 : ℝ) : ℂ) + t * Complex.I) *
              (((n : ℝ) * x : ℝ) : ℂ) ^ (((-1 / 16 : ℝ) : ℂ) + t * Complex.I))) =
        ((Real.exp (-((n : ℝ) * x)⁻¹) - 1 : ℝ) : ℂ) := by
      simpa only [Complex.real_smul] using he
    simp only [reflected_euler_term_factor a hx hn, MeasureTheory.integral_const_mul]
    rw [mul_left_comm _ (a n * _), hΓ]
    dsimp only [Analysis.reflectedEulerKernel]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one]
    ring

/-- For any Dirichlet character and positive scale, the actual normalized reflected
Euler integral equals the absolutely convergent inverted-kernel series. Combine the
weighted integral exchange with the exact individual inversion. This connects the
previous series estimate to an actual contour integral. -/
theorem gamma_reflected_euler_integral_eq_series {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries ((fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
              (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
            gammaSignedLeftWeight x t)) =
      ∑' n : ℕ,
        (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          (Analysis.reflectedEulerKernel x n : ℂ) := by
  rw [gamma_reflected_euler_integral_exchange χ hx, ← tsum_mul_left]
  apply tsum_congr
  intro n
  exact gamma_reflected_euler_term_integral _ hx n

/-- For any Dirichlet character and positive scale, the actual normalized Euler
integral is bounded by 1/(x sqrt x). Use the exact inverted-series identity and its
proved norm bound. No GRH or primitivity is needed. -/
theorem norm_gamma_reflected_euler_integral_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            LSeries ((fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
                (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
              gammaSignedLeftWeight x t))‖ ≤
      1 / (x * Real.sqrt x) := by
  rw [gamma_reflected_euler_integral_eq_series χ hx]
  exact Analysis.norm_twisted_reflectedEuler_tsum_le χ hx

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a positive level and any real height, the negative ordinary logarithmic
derivative on the reflected line equals its absolutely convergent Mangoldt Euler
series. Specialize the Dirichlet-series identity at real part 17/16. This supplies
the ordinary L-function form of the contour bound. -/
theorem gamma_reflected_ordinary_eq_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    -logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) =
      LSeries ((fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)))
        (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) := by
  have hs : 1 < (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only
  have h := lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hs
  simpa only [logDeriv, Pi.div_apply, Pi.mul_def, neg_div] using h.symm

/-- For any character of positive level and positive scale, the normalized actual
ordinary-logarithmic-derivative integral has norm at most 1/(x sqrt x).
Rewrite it as the reflected Euler integral. This separates the ordinary cost from
the remaining completed archimedean contribution. -/
theorem norm_gamma_reflected_ordinary_logDeriv_integral_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
              gammaSignedLeftWeight x t))‖ ≤
      1 / (x * Real.sqrt x) := by
  simp only [gamma_reflected_ordinary_eq_euler]
  exact norm_gamma_reflected_euler_integral_le χ hx

/-- For any positive-level character and positive scale, the actual reflected
ordinary logarithmic derivative times the Gamma weight is integrable. Sum the
integrable Euler terms using summable integral norms. This justifies splitting
the completed integral into its ordinary and archimedean parts. -/
theorem integrable_gamma_reflected_ordinary_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          gammaSignedLeftWeight x t) := by
  let f := (fun n : ℕ ↦ χ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  let F := fun (n : ℕ) (t : ℝ) ↦
    LSeries.term f (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) n * gammaSignedLeftWeight x t
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show 1 < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have hi :=
    Analysis.integrable_tsum_of_summable_integral_norm F
      (fun n ↦
        AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight _ (17 / 16) n
          (fun t : ℝ ↦ -t) continuous_neg (gammaSignedLeftWeight x)
          (integrable_gammaSignedLeftWeight hx))
      (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
        (fun t : ℝ ↦ -t) (gammaSignedLeftWeight x))
  have he (t : ℝ) :
    (∑' n, F n t) =
      -(logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
          gammaSignedLeftWeight x t) := by
    dsimp only [F]
    rw [tsum_mul_right]
    change LSeries f _ * _ = _
    rw [← gamma_reflected_ordinary_eq_euler]
    ring
  simpa only [Pi.neg_def, neg_neg] using (hi.congr (MeasureTheory.ae_of_all _ he)).neg

/-- The actual normalized reflected integral of completed minus ordinary logarithmic
derivatives at scale x. It isolates the archimedean factor without estimating it
by a combined conductor-free norm. The following exact split identifies its role
in the original completed left integral. -/
noncomputable def gammaReflectedArchimedeanIntegral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ,
      (logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) -
          logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ))) *
        gammaSignedLeftWeight x t)

/-- For primitive nonprincipal data with nonprincipal inverse and positive scale,
split the original completed left integral into the exact signed conductor term,
the inverse character's ordinary integral and its archimedean integral.
Use reflection and integral linearity with actual integrability. This retains
separate errors before applying the improved ordinary Euler estimate. -/
theorem gamma_signed_left_eq_ordinary_add_archimedean {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    gammaSignedLeftIntegral χ x =
      (Analysis.gammaNegativeConductorTerm (Real.log q) x : ℂ) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ,
            logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
              gammaSignedLeftWeight x t) +
        gammaReflectedArchimedeanIntegral χ⁻¹ x := by
  have hr := integrable_gammaSignedLeftRemainder hp hne hinv hx
  have hi := integrable_gamma_reflected_ordinary_logDeriv χ⁻¹ hx
  have he (t : ℝ) :
    gammaSignedLeftIntegrand χ x t - Complex.log (q : ℂ) * gammaSignedLeftWeight x t =
      logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
        gammaSignedLeftWeight x t := by
    rw [gammaSignedLeftIntegrand_reflection hp hne hinv, add_mul, add_sub_cancel_left]
  have hc := hr.congr (MeasureTheory.ae_of_all _ he)
  rw [gammaSignedLeftIntegral_eq_conductor_add_remainder hp hne hinv hx]
  simp only [he]
  dsimp only [gammaReflectedArchimedeanIntegral]
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub hc hi]
  ring

/-- For primitive nonprincipal data and positive scale, the original completed left
integral is bounded in real part by the signed conductor term, the actual
archimedean integral norm and 1/(x sqrt x). Apply the exact split and the Euler
integral bound. No uniform archimedean bound is assumed or claimed. -/
theorem re_gamma_signed_left_le_archimedean_add_euler {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    (gammaSignedLeftIntegral χ x).re ≤
      Analysis.gammaNegativeConductorTerm (Real.log q) x +
        ‖gammaReflectedArchimedeanIntegral χ⁻¹ x‖ +
        1 / (x * Real.sqrt x) := by
  have he := gamma_signed_left_eq_ordinary_add_archimedean hp hne hinv hx
  have hn := norm_gamma_reflected_ordinary_logDeriv_integral_le χ⁻¹ hx
  simp only [neg_mul, MeasureTheory.integral_neg, mul_neg, norm_neg] at hn
  have ho :=
    Complex.re_le_norm
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          logDeriv χ⁻¹.LFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) *
            gammaSignedLeftWeight x t)
  have ha := Complex.re_le_norm (gammaReflectedArchimedeanIntegral χ⁻¹ x)
  rw [he]
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith only [hn, ho, ha]

/-- For primitive nonprincipal data under GRH, ambient level at least 20000 and
scale at least two, bound the actual summand-plus-zero remainder by the pole
cost, signed conductor term, actual archimedean norm and 1/(x sqrt x).
Insert the split left integral into the completed residue identity and retain
the nonpositive right integral. This connects the Euler improvement to the
remainder used by witness comparisons. -/
theorem re_gamma_primitive_remainder_le_archimedean_add_euler {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x) :
    ((∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)).re ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        PseudoPrime.Analysis.gammaNegativeConductorTerm (Real.log m) x +
        ‖gammaReflectedArchimedeanIntegral χ⁻¹ x‖ +
        1 / (x * Real.sqrt x) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
      (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hx1 : 1 ≤ x := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx
  have hr : (S - (P - Z + J)).re ≤ 0 := by
    have h :=
      MellinKernel.tsum_summand_eq_completed_residue_formula gammaMellinKernel
        (by linarith only [hm] : 2 ≤ m) hGRH hp hne hinv (a := -9 / 16) (b := 9 / 16)
        (by norm_num only)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
    dsimp only at h
    dsimp only [S, P, Z, J]
    rw [h, add_sub_cancel_left]
    exact
      gamma_right_integral_re_nonpos χ (by norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hx
  have hP0 := gamma_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := hP0
  have hJ :
    J.re ≤
      PseudoPrime.Analysis.gammaNegativeConductorTerm (Real.log m) x +
        ‖gammaReflectedArchimedeanIntegral χ⁻¹ x‖ +
        1 / (x * Real.sqrt x) := by
    have h := re_gamma_signed_left_le_archimedean_add_euler hp hne hinv (zero_lt_one.trans_le hx1)
    rw [gammaSignedLeftIntegral_eq_original] at h
    exact h
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change (S + Z).re ≤ _
  rw [he]
  simp only [Complex.add_re]
  linarith only [hr, hP, hJ, Complex.re_le_norm P]

end PseudoPrime.LLS.PaperStatements
