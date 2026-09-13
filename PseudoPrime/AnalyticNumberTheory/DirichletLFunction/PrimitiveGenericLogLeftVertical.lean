/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveQuadraticLogLeftVertical

/-! Generic logarithmic left-vertical estimates and their height-sequence limits. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a primitive nontrivial character with nontrivial inverse,
`x > 0`, and `A ≥ 2`.
Conclusion: the logarithmic kernel is continuous on the generic left-vertical line.
Content: Functional-equation left-vertical nonvanishing supplies the regularity hypothesis for the
logarithmic
kernel; the affine parametrization is continuous.
Role: measurability input for the generic left-vertical integrability theorem.
-/
theorem continuous_dirichletLogContourKernel_leftVertical_line {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Continuous
      (fun t : ℝ =>
        dirichletLogContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hg : Continuous (fun t : ℝ => ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hOn :
    ContinuousOn (dirichletLogContourKernel x χ)
      (Set.range (fun t : ℝ => ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    rintro s ⟨t, rfl⟩
    have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hsre : (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -(A : ℝ) - 1 / 2 := by
      simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
        Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
        div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hsre_neg : (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re < 0 := by
      rw [hsre]
      linarith
    have hs0 : ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hsre_neg
      linarith
    have hL :=
      dirichletLFunction_ne_zero_leftVertical
        hprimitive hne hinv A hA t
    have hcont :=
      (differentiableAt_dirichletLogContourKernel
          hx hne hs0 hL).continuousAt
    exact hcont.continuousWithinAt
  exact hOn.comp_continuous hg (fun t => Set.mem_range_self t)

/--
Input/assumptions: the hypotheses of
`DirichletLFunction.continuous_dirichletLogContourKernel_leftVertical_line`.
Conclusion: the generic logarithmic left-vertical kernel is integrable on the whole real line.
Content: the generic `L'/L` envelope is dominated by the already established integrable
`General.logQuadraticEnvelope`; no quadratic character hypothesis is used.
Role: supplies the whole-line integral interface for the generic logarithmic contour.
-/
theorem integrable_dirichletLogContourKernel_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        dirichletLogContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le_general
      hprimitive hne hinv
  apply
    MeasureTheory.Integrable.mono'
      (General.integrable_logQuadraticEnvelope.const_mul
        (D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1)))
  · exact
      (continuous_dirichletLogContourKernel_leftVertical_line
          hprimitive hne hinv hx hA).aestronglyMeasurable
  · filter_upwards with t
    exact
      norm_dirichletLogContourKernel_leftVertical_envelope_le
        hx hA hDnn (fun t => hD A hA t) t

/--
For any character, `x > 0`, `A ≥ 2`, and a nonnegative coefficient `D` in the stated
pointwise `L'/L` bound, the whole-line logarithmic integral is bounded by
`D * x^(-A-1/2) * ((A+5)²+1) * logQuadraticEnvelopeMass`.
Integrate the envelope majorant. No primitivity, nontriviality, or GRH is assumed.
-/
theorem norm_integral_dirichletLogContourKernel_leftVertical_of_bound {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {D : ℝ} (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction χ)
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖∫ t : ℝ,
          dirichletLogContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
        General.logQuadraticEnvelopeMass := by
  have hg :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
          General.logQuadraticEnvelope t) :=
    General.integrable_logQuadraticEnvelope.const_mul _
  have hbound :=
    MeasureTheory.norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall fun t =>
        norm_dirichletLogContourKernel_leftVertical_envelope_le
          hx hA hDnn hLbound t)
  rwa [MeasureTheory.integral_const_mul] at hbound

/--
Input/assumptions: a primitive nontrivial character with nontrivial inverse and `x > 1`.
Conclusion: the generic logarithmic whole-line left-vertical integral tends to zero as `A → ∞`.
Content: factor `x^(-A-1/2)` into `x^(-1/2) (x⁻¹)^A`, dominate the polynomial coefficient by
`26 (A+1)²`, and apply geometric-polynomial decay.
Role: removes the generic logarithmic left-vertical term from the contour limit.
-/
theorem tendsto_dirichletLogContourKernel_leftVertical_integral_atTop {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun A : ℕ =>
        ∫ t : ℝ,
          dirichletLogContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le_general
      hprimitive hne hinv
  have hMassnn : (0 : ℝ) ≤ General.logQuadraticEnvelopeMass :=
    General.logQuadraticEnvelopeMass_nonneg
  set r : ℝ := x⁻¹ with hr_def
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr_def]
    positivity
  have hr1 : r < 1 := by
    rw [hr_def]
    exact inv_lt_one_of_one_lt₀ hx
  have hxpow_split : ∀ A : ℕ, x ^ (-(A : ℝ) - 1 / 2) = x ^ (-(1 : ℝ) / 2) * r ^ A := by
    intro A
    rw [hr_def, show -(A : ℝ) - 1 / 2 = -(1 : ℝ) / 2 + -(A : ℝ) by ring, Real.rpow_add hxpos,
      Real.rpow_neg hxpos.le, Real.rpow_natCast, ← inv_pow]
  have hpoly_le : ∀ A : ℕ, ((A : ℝ) + 5) ^ 2 + 1 ≤ 26 * (((A : ℝ) + 1) ^ 2) := by
    intro A
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    nlinarith [sq_nonneg (A : ℝ)]
  set K : ℝ :=
    D * x ^ (-(1 : ℝ) / 2) * General.logQuadraticEnvelopeMass *
      26 with
    hK_def
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK_def]
    positivity
  have hbound :
    ∀ A : ℕ,
      2 ≤ A →
        ‖∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
    intro A hA
    have hI :=
      norm_integral_dirichletLogContourKernel_leftVertical_of_bound
        hxpos hA hDnn (fun t => hD A hA t)
    have hxApow_nn : (0 : ℝ) ≤ x ^ (-(1 : ℝ) / 2) := (Real.rpow_pos_of_pos hxpos _).le
    have hrApow_nn : (0 : ℝ) ≤ r ^ A := by positivity
    calc
      ‖∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
            General.logQuadraticEnvelopeMass :=
        hI
      _ =
          D * (x ^ (-(1 : ℝ) / 2) * r ^ A) * (((A : ℝ) + 5) ^ 2 + 1) *
            General.logQuadraticEnvelopeMass :=
        by rw [hxpow_split A]
      _ ≤
          D * (x ^ (-(1 : ℝ) / 2) * r ^ A) * (26 * (((A : ℝ) + 1) ^ 2)) *
            General.logQuadraticEnvelopeMass :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpoly_le A) (by positivity)) hMassnn
      _ = K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
        rw [hK_def]
        ring
  have hgeom :
    Filter.Tendsto (fun A : ℕ => K * (((A : ℝ) + 1) ^ 2 * r ^ A)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun A : ℕ => ((A : ℝ) + 1) ^ 2 * r ^ A) Filter.atTop (nhds 0) :=
      General.tendsto_add_one_pow_mul_pow_of_lt_one 2 hr0 hr1
    simpa only [mul_zero] using h1.const_mul K
  apply squeeze_zero_norm' (a := fun A : ℕ => K * (((A : ℝ) + 1) ^ 2 * r ^ A))
  · filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact hbound A hA
  · exact hgeom

/--
For a primitive nontrivial character with nontrivial inverse, `x > 0`, and `A ≥ 2`,
the integrals on `[-T,T]` converge to the whole-line logarithmic integral as real `T → ∞`.
Apply interval-integral exhaustion to the established whole-line integrability.
This statement needs no GRH and precedes specialization to the GRH height sequence.
-/
theorem tendsto_intervalIntegral_dirichletLogContourKernel_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ t in (-T)..T,
          dirichletLogContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletLogContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℝ) + (t : ℂ) * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_dirichletLogContourKernel_leftVertical
      hprimitive hne hinv hx hA)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/--
The preceding fixed-`A` convergence specialized to the generic GRH height sequence.
-/
theorem tendsto_primitiveHorizontalHeightSeq_log_leftVertical_intervalIntegral {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {A : ℕ}
    (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ t in
          (-(primitiveHorizontalHeightSeq_of_grh
              hN2 hGRH hprimitive hne hinv
              k))..(primitiveHorizontalHeightSeq_of_grh
            hN2 hGRH hprimitive hne hinv k),
          dirichletLogContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletLogContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  (tendsto_intervalIntegral_dirichletLogContourKernel_leftVertical
        hprimitive hne hinv hx hA).comp
    (tendsto_primitiveHorizontalHeightSeq_atTop_of_grh
      hN2 hGRH hprimitive hne hinv)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
