/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.General.VerticalGeometry
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLeftVerticalBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveQuadraticLogHorizontalBound

/-!
# Left-vertical bounds and vanishing integrals for the logarithmic kernel

For the logarithmic kernel, prove the counterparts of the reciprocal-kernel estimates in
`PrimitiveLeftVerticalBound`.
The `L'/L` growth ingredient (`exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le`) and the
universal integrable envelope (`PseudoPrime.AnalyticNumberTheory.General.logQuadraticEnvelope`,
`General.integrable_logQuadraticEnvelope`) are kernel-independent and reused as-is; only the
kernel-specific wrapping changes. The Mellin factor `x^s/s²` has one pole location, `s = 0`, of
order two, so its denominator lower bound uses `‖s‖²` directly (`1 + t² ≤ ‖s_A(t)‖²`, needing
only `(A + 1/2)² ≥ 1`) rather than the reciprocal kernel's `‖s‖ * ‖s - 1‖` product, and its
power-of-`x`
exponent is `-A - 1/2` (matching `s.re` directly) rather than `-A - 3/2` (matching `(s - 1).re`) —
still strictly negative, hence geometrically decaying in `A` when `x > 1`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The left-vertical line's log-kernel geometry -/

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `t : ℝ`, and a bound `‖logDeriv (LFunction χ) (s_A(t))‖ ≤
D ((A + 5)² + 1 + log(|t| + 2))`.
Conclusion: `‖DirichletLFunction.dirichletLogContourKernel x χ (s_A(t))‖ ≤
D x^(-A - 1/2) ((A + 5)² + 1 + log(|t| + 2)) / (1 + t²)`.
Content: unfolds the kernel to `‖logDeriv (LFunction χ) s‖ * ‖x ^ s‖ / ‖s‖²`, then substitutes
`‖x ^ s‖ = x^(-A-1/2)` (`General.norm_cpow_leftVertical_log`) and divides through by the
denominator lower
bound `1 + t² ≤ ‖s‖²` (`General.one_add_sq_le_normSq_leftVertical`).
Role: the log-kernel pointwise bound (K), feeding the absolute-integrability argument.
-/
theorem norm_dirichletLogContourKernel_leftVertical_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {t D : ℝ}
    (hL :
      ‖logDeriv (DirichletCharacter.LFunction χ)
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / (1 + t ^ 2) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hden := General.one_add_sq_le_normSq_leftVertical A hA t
  rw [← hs_def] at hden
  have hpow := General.norm_cpow_leftVertical_log hx A t
  rw [← hs_def] at hpow
  have hsnorm_pos : (0 : ℝ) < ‖s‖ ^ 2 := by
    have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
    linarith [hden]
  have hK_eq :
    ‖dirichletLogContourKernel x χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 1 / 2) / ‖s‖ ^ 2 := by
    have hlogDeriv_eq :
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [logDeriv_apply]
    unfold dirichletLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hpow, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have hLnn : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := norm_nonneg _
  have hxpow_pos : (0 : ℝ) < x ^ (-(A : ℝ) - 1 / 2) := Real.rpow_pos_of_pos hx _
  have h1t_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 1 / 2) / ‖s‖ ^ 2 ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 1 / 2) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) h1t_pos hden
    _ ≤ D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) * x ^ (-(A : ℝ) - 1 / 2) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL hxpow_pos.le) h1t_pos.le
    _ = D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / (1 + t ^ 2) :=
      by ring

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 0`, `A ≥ 2`.
Conclusion: `t ↦ DirichletLFunction.dirichletLogContourKernel x χ (s_A(t))` is continuous on `ℝ`.
Content: nonvanishing of `L` at every `s_A(t)`
(`DirichletLFunction.quadraticDirichletLFunction_ne_zero_leftVertical`, kernel-independent, reused
as-is) plus
`s_A(t) ≠ 0` gives pointwise `DifferentiableAt` of the log kernel
(`DirichletLFunction.differentiableAt_dirichletLogContourKernel`), hence `ContinuousAt`.
Role: supplies the `AEStronglyMeasurable` input for the log kernel's absolute integrability.
-/
private theorem quadContinuousLogKernel_leftVertical {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) {A : ℕ}
    (hA : 2 ≤ A) :
    Continuous
      (fun t : ℝ ↦
        dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hg : Continuous (fun t : ℝ ↦ ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hOn :
    ContinuousOn (dirichletLogContourKernel x χ)
      (Set.range (fun t : ℝ ↦ ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    rintro s ⟨t, rfl⟩
    have hsre : (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -(A : ℝ) - 1 / 2 := by
      simp only [one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
        Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
        Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
        div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have hsre_neg : (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re < 0 := by
      rw [hsre]; linarith
    have hs0 : ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hsre_neg; linarith
    have hL := quadraticDirichletLFunction_ne_zero_leftVertical hprimitive hne hquad A hA t
    exact (differentiableAt_dirichletLogContourKernel hx hne hs0 hL).continuousAt.continuousWithinAt
  exact hOn.comp_continuous hg (fun t => Set.mem_range_self t)

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `D ≥ 0` with the pointwise `L'/L` bound
`‖logDeriv (LFunction χ) (s_A(t))‖ ≤ D ((A + 5)² + 1 + log(|t| + 2))` for every `t`.
Conclusion: `‖K_x(s_A(t))‖ ≤ D x^{-A-1/2} ((A + 5)² + 1) · General.logQuadraticEnvelope t`.
Content: same algebra as
`DirichletLFunction.norm_dirichletReciprocalContourKernel_leftVertical_envelope_le`,
substituting the log-kernel pointwise bound `(K)` and its `x^{-A-1/2}` power factor.
Role: the log-kernel envelope bound, using the integrable function `logQuadraticEnvelope`.
-/
theorem norm_dirichletLogContourKernel_leftVertical_envelope_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {D : ℝ} (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction χ)
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)))
    (t : ℝ) :
    ‖dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) * General.logQuadraticEnvelope t := by
  have hK := norm_dirichletLogContourKernel_leftVertical_le hx hA (hLbound t)
  set BA : ℝ := ((A : ℝ) + 5) ^ 2 + 1 with hBA_def
  have hBA1 : (1 : ℝ) ≤ BA := by
    rw [hBA_def]; nlinarith [sq_nonneg ((A : ℝ) + 5)]
  have htlog_nn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have htsq_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hxpow_nn : (0 : ℝ) ≤ x ^ (-(A : ℝ) - 1 / 2) := (Real.rpow_pos_of_pos hx _).le
  have hstep : BA + Real.log (|t| + 2) ≤ BA * (1 + Real.log (|t| + 2)) := by
    nlinarith [hBA1, htlog_nn]
  have hnum :
    D * x ^ (-(A : ℝ) - 1 / 2) * (BA + Real.log (|t| + 2)) ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (BA * (1 + Real.log (|t| + 2))) :=
    mul_le_mul_of_nonneg_left hstep (mul_nonneg hDnn hxpow_nn)
  unfold General.logQuadraticEnvelope
  calc
    ‖dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * x ^ (-(A : ℝ) - 1 / 2) * (BA + Real.log (|t| + 2)) / (1 + t ^ 2) :=
      hK
    _ ≤ D * x ^ (-(A : ℝ) - 1 / 2) * (BA * (1 + Real.log (|t| + 2))) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right hnum htsq_pos.le
    _ = D * x ^ (-(A : ℝ) - 1 / 2) * BA * ((1 + Real.log (|t| + 2)) / (1 + t ^ 2)) := by ring

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 0`, `A ≥ 2`.
Conclusion: `t ↦ DirichletLFunction.dirichletLogContourKernel x χ (s_A(t))` is integrable over `ℝ`.
Content: `exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le` (kernel-independent, reused as-
is) supplies the `L'/L` bound feeding `(K')`; the scaled envelope is integrable
(`General.integrable_logQuadraticEnvelope.const_mul`); `Integrable.mono'` finishes.
Role: the log-kernel integrability, feeding both the whole-line integral norm bound (I) and the
fixed-`A` truncation-to-whole-line limit.
-/
private theorem quadIntegrableLogKernel_leftVertical {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) {A : ℕ}
    (hA : 2 ≤ A) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le hprimitive hne hquad
  apply
    MeasureTheory.Integrable.mono'
      ((General.integrable_logQuadraticEnvelope.const_mul
        (D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1))))
  · exact (quadContinuousLogKernel_leftVertical hprimitive hne hquad hx hA).aestronglyMeasurable
  · filter_upwards with t
    exact norm_dirichletLogContourKernel_leftVertical_envelope_le hx hA hDnn (fun t => hD A hA t) t

/-! ### The whole-line integral norm bound (I), log kernel -/

/-- For `x > 0` and `A ≥ 2`, a nonnegative coefficient in the pointwise logarithmic-derivative
bound gives an upper bound for the norm of the whole-line kernel integral. Integrate the
`logQuadraticEnvelope` majorant; no quadratic-character hypothesis is needed for this estimate. -/
private theorem quadraticNorm_integral_dirichletLogContourKernel_leftVertical_of_bound {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {D : ℝ}
    (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction χ)
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖∫ t : ℝ, dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) * General.logQuadraticEnvelopeMass := by
  have hg :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) * General.logQuadraticEnvelope t) :=
    General.integrable_logQuadraticEnvelope.const_mul _
  have hbound :=
    MeasureTheory.norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall fun t =>
        norm_dirichletLogContourKernel_leftVertical_envelope_le hx hA hDnn hLbound t)
  rwa [MeasureTheory.integral_const_mul] at hbound

/-! ### Fixed-`A` truncated vertical → whole-line, log kernel -/

/-- For a primitive nontrivial quadratic character, `x > 0`, and `A ≥ 2`, the integrals on
`[-T,T]` converge to the whole-line logarithmic-kernel integral as `T → ∞`. This follows from
absolute integrability and supplies the limit along the selected contour heights. -/
private theorem quadraticTendsto_intervalIntegral_dirichletLogContourKernel_leftVertical {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ t in (-T)..T,
          dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (quadIntegrableLogKernel_leftVertical hprimitive hne hquad hx hA)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/-- Log-kernel analogue of
`DirichletLFunction.tendsto_primitiveHorizontalHeightSeq_leftVertical_intervalIntegral`. -/
theorem quadraticTendsto_primitiveHorizontalHeightSeq_log_leftVertical_intervalIntegral {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ∫ t in
          (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
              k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
          dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  (quadraticTendsto_intervalIntegral_dirichletLogContourKernel_leftVertical hprimitive hne hquad hx
        hA).comp
    (tendsto_primitiveHorizontalHeightSeq_atTop hN2 hGRH hprimitive hne hinv hquad)

/-! ### `A → ∞`: the fixed-`A` whole-line integral vanishes, log kernel -/

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 1`.
Conclusion: `A ↦ ∫ t, K_x(s_A(t))` tends to `0` as `A → ∞`, for the log kernel.
Content: `x^{-A-1/2} = x^{-1/2} (x⁻¹)^A` and `(A + 5)² + 1 ≤ 26 (A + 1)²` reduce the whole-line
integral norm bound (I) to `‖∫ K‖ ≤ K₀ ((A + 1)² (x⁻¹)^A)`; since `0 ≤ x⁻¹ < 1` (from `x > 1`),
`General.tendsto_add_one_pow_mul_pow_of_lt_one` gives `(A + 1)² (x⁻¹)^A → 0`, and
`squeeze_zero_norm`
finishes. Identical structure to
`DirichletLFunction.tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop`, only the
power-of-`x`
exponent shifts from `-3/2` to `-1/2`.
Role: the left-vertical edge integral
vanishes as `A → ∞`, matching the log kernel's horizontal-edge vanishing to close the primitive
log-kernel explicit-formula contour on the left.
-/
theorem quadraticTendsto_dirichletLogContourKernel_leftVertical_integral_atTop {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun A : ℕ ↦
        ∫ t : ℝ, dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le hprimitive hne hquad
  have hMassnn : (0 : ℝ) ≤ General.logQuadraticEnvelopeMass :=
    General.logQuadraticEnvelopeMass_nonneg
  set r : ℝ := x⁻¹ with hr_def
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr_def]; positivity
  have hr1 : r < 1 := by
    rw [hr_def]; exact inv_lt_one_of_one_lt₀ hx
  have hxpow_split : ∀ A : ℕ, x ^ (-(A : ℝ) - 1 / 2) = x ^ (-(1 : ℝ) / 2) * r ^ A := by
    intro A
    rw [hr_def, show -(A : ℝ) - 1 / 2 = -(1 : ℝ) / 2 + -(A : ℝ) from by ring, Real.rpow_add hxpos,
      Real.rpow_neg hxpos.le, Real.rpow_natCast, ← inv_pow]
  have hpoly_le : ∀ A : ℕ, ((A : ℝ) + 5) ^ 2 + 1 ≤ 26 * (((A : ℝ) + 1) ^ 2) := by
    intro A
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    nlinarith [sq_nonneg (A : ℝ)]
  set K : ℝ := D * x ^ (-(1 : ℝ) / 2) * General.logQuadraticEnvelopeMass * 26 with hK_def
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK_def]; positivity
  have hbound :
    ∀ A : ℕ,
      2 ≤ A →
        ‖∫ t : ℝ,
              dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
    intro A hA
    have hI :=
      quadraticNorm_integral_dirichletLogContourKernel_leftVertical_of_bound hxpos hA hDnn
        (fun t => hD A hA t)
    have hxApow_nn : (0 : ℝ) ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos _ |>.le
    have hrApow_nn : (0 : ℝ) ≤ r ^ A := by positivity
    calc
      ‖∫ t : ℝ,
              dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * x ^ (-(A : ℝ) - 1 / 2) * (((A : ℝ) + 5) ^ 2 + 1) * General.logQuadraticEnvelopeMass :=
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
        rw [hK_def]; ring
  have hgeom :
    Filter.Tendsto (fun A : ℕ ↦ K * (((A : ℝ) + 1) ^ 2 * r ^ A)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun A : ℕ ↦ ((A : ℝ) + 1) ^ 2 * r ^ A) Filter.atTop (nhds 0) :=
      General.tendsto_add_one_pow_mul_pow_of_lt_one 2 hr0 hr1
    simpa only [mul_zero] using h1.const_mul K
  apply squeeze_zero_norm' (a := fun A : ℕ ↦ K * (((A : ℝ) + 1) ^ 2 * r ^ A))
  · filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact hbound A hA
  · exact hgeom

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
