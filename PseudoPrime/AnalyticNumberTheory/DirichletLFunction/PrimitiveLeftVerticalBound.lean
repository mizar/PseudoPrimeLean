/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.General.VerticalGeometry
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalNonvanishing
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalLBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SmoothedContour
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound
import PseudoPrime.AnalyticNumberTheory.General.GeometricDecay
import PseudoPrime.AnalyticNumberTheory.General.LogQuadraticEnvelope

/-!
# Left-vertical reciprocal-kernel estimates and integral limits

On `s_A(t) = -A-1/2+it`, the power factor has norm `x^(-A-3/2)` and
`1+t² ≤ ‖s_A(t)‖ * ‖s_A(t)-1‖`. Combine these with the logarithmic-derivative bound
and the integrable logarithmic envelope to prove continuity, integrability, truncation
limits, and vanishing as `A → ∞` for `x > 1`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The left-vertical line's geometry -/

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `t : ℝ`, and a bound `‖logDeriv (LFunction χ) (s_A(t))‖ ≤
D ((A + 5)² + 1 + log(|t| + 2))`.
Conclusion: `‖DirichletLFunction.dirichletReciprocalContourKernel x χ (s_A(t))‖ ≤
D x^(-A - 3/2) ((A + 5)² + 1 + log(|t| + 2)) / (1 + t²)`.
Content: unfolds the kernel to `‖logDeriv (LFunction χ) s‖ * ‖x ^ (s - 1)‖ / (‖s‖ * ‖s - 1‖)`, then
substitutes `‖x ^ (s - 1)‖ = x^(-A-3/2)` (`General.norm_cpow_leftVertical_sub_one`) and divides
through by
the denominator lower bound `1 + t² ≤ ‖s‖ * ‖s - 1‖`
(`General.one_add_sq_le_norm_mul_norm_leftVertical`).
Role: the left-vertical integral argument pointwise kernel bound (K), feeding the
absolute-integrability argument.
-/
theorem norm_dirichletReciprocalContourKernel_leftVertical_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {t D : ℝ}
    (hL :
      ‖logDeriv (DirichletCharacter.LFunction χ)
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖dirichletReciprocalContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / (1 + t ^ 2) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hden :=
    General.one_add_sq_le_norm_mul_norm_leftVertical A hA t
  rw [← hs_def] at hden
  have hpow := General.norm_cpow_leftVertical_sub_one hx A t
  rw [← hs_def] at hpow
  have hsnorm_pos : (0 : ℝ) < ‖s‖ * ‖s - 1‖ := by
    have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
    linarith [hden]
  have hK_eq :
    ‖dirichletReciprocalContourKernel x χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 3 / 2) / (‖s‖ * ‖s - 1‖) := by
    have hlogDeriv_eq :
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [logDeriv_apply]
    unfold dirichletReciprocalContourKernel
    rw [norm_div, norm_mul, norm_neg, hpow, hlogDeriv_eq, norm_mul]
  rw [hK_eq]
  have hLnn : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := norm_nonneg _
  have hxpow_pos : (0 : ℝ) < x ^ (-(A : ℝ) - 3 / 2) := Real.rpow_pos_of_pos hx _
  have h1t_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 3 / 2) / (‖s‖ * ‖s - 1‖) ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (-(A : ℝ) - 3 / 2) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) h1t_pos hden
    _ ≤ D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) * x ^ (-(A : ℝ) - 3 / 2) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hL hxpow_pos.le) h1t_pos.le
    _ = D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)) / (1 + t ^ 2) :=
      by ring

/-! ### A single universal integrable envelope, no tail/compact split needed -/

/-! ### Nonvanishing, continuity, and integrability of the kernel on the left-vertical line -/

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 0`, `A : ℕ` with `2 ≤ A`.
Conclusion: `t ↦ DirichletLFunction.dirichletReciprocalContourKernel x χ (s_A(t))` is continuous on
`ℝ`.
Content: nonvanishing of `L` at every `s_A(t)` (`quadraticDirichletLFunction_ne_zero_leftVertical`)
plus `s_A(t) ≠ 0, 1` (its real
part is `≤ -5/2 < 0`) gives pointwise `DifferentiableAt` of the kernel
(`DirichletLFunction.differentiableAt_dirichletReciprocalContourKernel`), hence `ContinuousAt`;
composing with the
continuous affine map `t ↦ s_A(t)` finishes.
Role: supplies the `AEStronglyMeasurable` input for the kernel's absolute integrability.
-/
private theorem quadraticContinuousReciprocalKernel_leftVertical_line {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Continuous
      (fun t : ℝ ↦
        dirichletReciprocalContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hg : Continuous (fun t : ℝ ↦ ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hOn :
    ContinuousOn
      (dirichletReciprocalContourKernel x χ)
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
    have hs1 : ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hsre_neg; linarith
    have hL :=
      quadraticDirichletLFunction_ne_zero_leftVertical
        hprimitive hne hquad A hA t
    exact
      (differentiableAt_dirichletReciprocalContourKernel
          hx hne hs0 hs1 hL).continuousAt.continuousWithinAt
  exact hOn.comp_continuous hg (fun t => Set.mem_range_self t)

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `D ≥ 0` with the pointwise `L'/L` bound
`‖logDeriv (LFunction χ) (s_A(t))‖ ≤ D ((A + 5)² + 1 + log(|t| + 2))` for every `t`.
Conclusion: `‖K_x(s_A(t))‖ ≤ D x^{-A-3/2} ((A + 5)² + 1) · General.logQuadraticEnvelope t`.
Content: `(K)` gives `‖K_x(s_A(t))‖ ≤ D x^{-A-3/2} (B_A + log(|t| + 2)) / (1 + t²)` with
`B_A := (A + 5)² + 1 ≥ 1`; since `log(|t| + 2) ≥ 0`, `B_A + log(|t| + 2) ≤ B_A (1 + log(|t| + 2))`
(`(B_A - 1) log(|t| + 2) ≥ 0`); dividing by `1 + t²` and unfolding `General.logQuadraticEnvelope`
finishes.
Role: the `(K')` envelope bound, uniformly scaling the universal integrable envelope `g` by an
`A`-dependent but `t`-independent constant, feeding the kernel's own integrability.
-/
theorem norm_dirichletReciprocalContourKernel_leftVertical_envelope_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {D : ℝ} (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction χ)
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2)))
    (t : ℝ) :
    ‖dirichletReciprocalContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
        General.logQuadraticEnvelope t := by
  have hK :=
    norm_dirichletReciprocalContourKernel_leftVertical_le
      hx hA (hLbound t)
  set BA : ℝ := ((A : ℝ) + 5) ^ 2 + 1 with hBA_def
  have hBA1 : (1 : ℝ) ≤ BA := by
    rw [hBA_def]; nlinarith [sq_nonneg ((A : ℝ) + 5)]
  have htlog_nn : (0 : ℝ) ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have htsq_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hxpow_nn : (0 : ℝ) ≤ x ^ (-(A : ℝ) - 3 / 2) := (Real.rpow_pos_of_pos hx _).le
  have hstep : BA + Real.log (|t| + 2) ≤ BA * (1 + Real.log (|t| + 2)) := by
    nlinarith [hBA1, htlog_nn]
  have hnum :
    D * x ^ (-(A : ℝ) - 3 / 2) * (BA + Real.log (|t| + 2)) ≤
      D * x ^ (-(A : ℝ) - 3 / 2) * (BA * (1 + Real.log (|t| + 2))) :=
    mul_le_mul_of_nonneg_left hstep (mul_nonneg hDnn hxpow_nn)
  unfold General.logQuadraticEnvelope
  calc
    ‖dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        D * x ^ (-(A : ℝ) - 3 / 2) * (BA + Real.log (|t| + 2)) / (1 + t ^ 2) :=
      hK
    _ ≤ D * x ^ (-(A : ℝ) - 3 / 2) * (BA * (1 + Real.log (|t| + 2))) / (1 + t ^ 2) :=
      div_le_div_of_nonneg_right hnum htsq_pos.le
    _ = D * x ^ (-(A : ℝ) - 3 / 2) * BA * ((1 + Real.log (|t| + 2)) / (1 + t ^ 2)) := by ring

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 0`, `A ≥ 2`.
Conclusion: `t ↦ DirichletLFunction.dirichletReciprocalContourKernel x χ (s_A(t))` is integrable
over `ℝ`.
Content: `exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le` supplies the `L'/L` bound
feeding `(K')`; the scaled envelope `D x^{-A-3/2} ((A+5)² + 1) • General.logQuadraticEnvelope` is
integrable (`General.integrable_logQuadraticEnvelope.const_mul`); `Integrable.mono'` with the
continuity-supplied `AEStronglyMeasurable` witness finishes.
Role: the left-vertical integral argument kernel integrability, feeding both the whole-line
integral norm bound (I) and the
fixed-`A` truncation-to-whole-line limit.
-/
private theorem quadraticIntegrableReciprocalKernel_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        dirichletReciprocalContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le
      hprimitive hne hquad
  apply
    MeasureTheory.Integrable.mono'
      ((General.integrable_logQuadraticEnvelope.const_mul
        (D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1))))
  · exact
      (quadraticContinuousReciprocalKernel_leftVertical_line
          hprimitive hne hquad hx hA).aestronglyMeasurable
  · filter_upwards with t
    exact
      norm_dirichletReciprocalContourKernel_leftVertical_envelope_le
        hx hA hDnn (fun t => hD A hA t) t

/-! ### The whole-line integral norm bound (I) -/

/--
Input/assumptions: `x > 0`, `A ≥ 2`, `D ≥ 0` with the pointwise `L'/L` bound
`‖logDeriv (LFunction χ) (s_A(t))‖ ≤ D ((A + 5)² + 1 + log(|t| + 2))` for every `t`.
Conclusion: `‖∫ t, K_x(s_A(t))‖ ≤ D x^{-A-3/2} ((A+5)² + 1) · General.logQuadraticEnvelopeMass`.
Content: `MeasureTheory.norm_integral_le_of_norm_le` with the scaled-envelope majorant
(`(K')`/`PseudoPrime.AnalyticNumberTheory.General.integrable_logQuadraticEnvelope.const_mul`) gives
`‖∫ K‖ ≤ ∫ (D x^{-A-3/2} ((A+5)² + 1)) • General.logQuadraticEnvelope`, which
`MeasureTheory.integral_const_mul` collapses to the scaled envelope mass.
Role: the explicit-`D` form of the left-vertical integral argument whole-line integral norm bound
(I), letting the `A → ∞`
vanishing argument reuse a single `D` obtained once (rather than re-deriving it, existentially, at
every `A`).
-/
theorem norm_integral_dirichletReciprocalContourKernel_leftVertical_of_bound {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) {D : ℝ} (hDnn : 0 ≤ D)
    (hLbound :
      ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.LFunction χ)
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (|t| + 2))) :
    ‖∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
        General.logQuadraticEnvelopeMass := by
  have hg :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
          General.logQuadraticEnvelope t) :=
    General.integrable_logQuadraticEnvelope.const_mul _
  have hbound :=
    MeasureTheory.norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall fun t =>
        norm_dirichletReciprocalContourKernel_leftVertical_envelope_le
          hx hA hDnn hLbound t)
  rwa [MeasureTheory.integral_const_mul] at hbound

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 0`, `A ≥ 2`.
Conclusion: `T ↦ ∫ t in -T..T, K_x(s_A(t))` tends to `∫ t, K_x(s_A(t))` as `T → ∞`.
Content: `MeasureTheory.intervalIntegral_tendsto_integral` fed by whole-line integrability
(`quadraticIntegrableReciprocalKernel_leftVertical`), with the endpoint filters
`-T → -∞` (`tendsto_neg_atTop_atBot'`) and `T → ∞` (`Filter.tendsto_id`).
Role: connects the fixed-`A` left-vertical edge of a growing finite rectangle to the whole-line
integral bounded by `(I)`.
-/
private theorem quadraticTendsto_intervalIntegralReciprocalKernel_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    {x : ℝ} (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ t in (-T)..T,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (quadraticIntegrableReciprocalKernel_leftVertical
      hprimitive hne hquad hx hA)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x > 0`,
`A ≥ 2`.
Conclusion: along the named height sequence `DirichletLFunction.primitiveHorizontalHeightSeq _ k`,
the fixed-`A`
truncated left-vertical integral tends to the fixed-`A` whole-line integral as `k → ∞`.
Content: composes the generic `T → ∞` truncation limit with
`DirichletLFunction.tendsto_primitiveHorizontalHeightSeq_atTop`, so that the same height sequence
used for the
horizontal edges (the horizontal argument) also drives the left-vertical edge's truncation,
matching a single growing
rectangle.
Role: the named-height-sequence wrapper needed for the shared-height argument's contour assembly
(all four edges of the
same finite rectangle, indexed by the same `k`).
-/
theorem quadraticTendsto_primitiveHorizontalHeightSeq_leftVertical_intervalIntegral {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ∫ t in
          (-(primitiveHorizontalHeightSeq hN2
              hGRH hprimitive hne hinv hquad
              k))..(primitiveHorizontalHeightSeq
            hN2 hGRH hprimitive hne hinv hquad k),
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  (quadraticTendsto_intervalIntegralReciprocalKernel_leftVertical
        hprimitive hne hquad hx hA).comp
    (tendsto_primitiveHorizontalHeightSeq_atTop
      hN2 hGRH hprimitive hne hinv hquad)

/--
Input/assumptions: `χ` primitive and nontrivial with nontrivial inverse, `x > 0`, and `A ≥ 2`.
Conclusion: the reciprocal contour kernel is continuous on the generic left vertical line.
Content: the generic inverse-character nonvanishing theorem replaces the quadratic-only input in
the existing continuity proof.
Role: supplies measurability for the generic left-vertical integrability proof.
-/
theorem continuous_dirichletReciprocalContourKernel_leftVertical_line {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Continuous
      (fun t : ℝ ↦
        dirichletReciprocalContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hg : Continuous (fun t : ℝ ↦ ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hOn :
    ContinuousOn
      (dirichletReciprocalContourKernel x χ)
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
      rw [hsre]
      linarith
    have hs0 : ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hsre_neg
      linarith
    have hs1 : ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hsre_neg
      linarith
    have hL :=
      dirichletLFunction_ne_zero_leftVertical
        hprimitive hne hinv A hA t
    exact
      (differentiableAt_dirichletReciprocalContourKernel
          hx hne hs0 hs1 hL).continuousAt.continuousWithinAt
  exact hOn.comp_continuous hg (fun t => Set.mem_range_self t)

/--
Input/assumptions: the generic left-vertical hypotheses, `x > 0`, and `A ≥ 2`.
Conclusion: the generic reciprocal kernel is integrable on the full left vertical line.
Content: applies the generic `L'/L` envelope bound to the existing integrable logarithmic envelope.
Role: permits the generic truncated-to-whole-line limit.
-/
theorem integrable_dirichletReciprocalContourKernel_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        dirichletReciprocalContourKernel x χ
          (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le_general
      hprimitive hne hinv
  apply
    MeasureTheory.Integrable.mono'
      ((General.integrable_logQuadraticEnvelope.const_mul
        (D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1))))
  · exact
      (continuous_dirichletReciprocalContourKernel_leftVertical_line
          hprimitive hne hinv hx hA).aestronglyMeasurable
  · filter_upwards with t
    exact
      norm_dirichletReciprocalContourKernel_leftVertical_envelope_le
        hx hA hDnn (fun t => hD A hA t) t

/--
Input/assumptions: the generic left-vertical hypotheses, `x > 0`, and `A ≥ 2`.
Conclusion: symmetric finite truncations converge to the generic whole-line left-edge integral.
Content: applies `intervalIntegral_tendsto_integral` to the preceding integrability theorem.
Role: is the fixed-`A` component for the shared-height contour limit.
-/
theorem tendsto_intervalIntegral_dirichletReciprocalContourKernel_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) {A : ℕ} (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ t in -T..T,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_dirichletReciprocalContourKernel_leftVertical
      hprimitive hne hinv hx hA)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/--
Input/assumptions: the generic primitive character hypotheses and GRH, with `x > 0` and `A ≥ 2`.
Conclusion: the shared horizontal-height sequence truncates the generic left edge to its whole-line
integral.
Content: composes the fixed-`A` generic truncation limit with the named height sequence tending to
infinity.
Role: connects the generic left edge to the same rectangles as the generic horizontal edges.
-/
theorem tendsto_primitiveHorizontalHeightSeq_leftVertical_intervalIntegral {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {A : ℕ}
    (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ ↦
        ∫ t in
          (-(primitiveHorizontalHeightSeq_of_grh
              hN2 hGRH hprimitive hne hinv
              k))..(primitiveHorizontalHeightSeq_of_grh
            hN2 hGRH hprimitive hne hinv k),
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) :=
  (tendsto_intervalIntegral_dirichletReciprocalContourKernel_leftVertical
        hprimitive hne hinv hx hA).comp
    (tendsto_primitiveHorizontalHeightSeq_atTop_of_grh
      hN2 hGRH hprimitive hne hinv)

/-! ### `A → ∞`: the fixed-`A` whole-line integral vanishes — the left-edge argument's completion -/

/-- Generic left-vertical whole-line integral vanishes as the left edge tends to `-∞`. -/
theorem tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun A : ℕ ↦
        ∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le_general
      hprimitive hne hinv
  set r : ℝ := x⁻¹ with hr_def
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr_def]; positivity
  have hr1 : r < 1 := by
    rw [hr_def]; exact inv_lt_one_of_one_lt₀ hx
  have hxpow_split : ∀ A : ℕ, x ^ (-(A : ℝ) - 3 / 2) = x ^ (-(3 : ℝ) / 2) * r ^ A := by
    intro A
    rw [hr_def, show -(A : ℝ) - 3 / 2 = -(3 : ℝ) / 2 + -(A : ℝ) from by ring, Real.rpow_add hxpos,
      Real.rpow_neg hxpos.le, Real.rpow_natCast, ← inv_pow]
  have hpoly_le : ∀ A : ℕ, ((A : ℝ) + 5) ^ 2 + 1 ≤ 26 * (((A : ℝ) + 1) ^ 2) := by
    intro A
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    nlinarith [sq_nonneg (A : ℝ)]
  set K : ℝ :=
    D * x ^ (-(3 : ℝ) / 2) * General.logQuadraticEnvelopeMass *
      26 with
    hK_def
  have hbound :
    ∀ A : ℕ,
      2 ≤ A →
        ‖∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
    intro A hA
    have hI :=
      norm_integral_dirichletReciprocalContourKernel_leftVertical_of_bound
        hxpos hA hDnn (fun t => hD A hA t)
    calc
      ‖∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
            General.logQuadraticEnvelopeMass :=
        hI
      _ =
          D * (x ^ (-(3 : ℝ) / 2) * r ^ A) * (((A : ℝ) + 5) ^ 2 + 1) *
            General.logQuadraticEnvelopeMass :=
        by rw [hxpow_split A]
      _ ≤
          D * (x ^ (-(3 : ℝ) / 2) * r ^ A) * (26 * (((A : ℝ) + 1) ^ 2)) *
            General.logQuadraticEnvelopeMass :=
        by
        have hMassnn :
          (0 : ℝ) ≤ General.logQuadraticEnvelopeMass :=
          General.logQuadraticEnvelopeMass_nonneg
        have hxpow_nn : (0 : ℝ) ≤ x ^ (-(3 : ℝ) / 2) := (Real.rpow_pos_of_pos hxpos _).le
        have hrpow_nn : (0 : ℝ) ≤ r ^ A := by positivity
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpoly_le A)
              (mul_nonneg hDnn (mul_nonneg hxpow_nn hrpow_nn)))
            hMassnn
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

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `x > 1`.
Conclusion: `A ↦ ∫ t, K_x(s_A(t))` tends to `0` as `A → ∞`.
Content: `x^{-A-3/2} = x^{-3/2} (x⁻¹)^A` and `(A + 5)² + 1 ≤ 26 (A + 1)²` (both `A`-uniform
algebraic facts) reduce the whole-line integral norm bound (I) to
`‖∫ K‖ ≤ K₀ ((A + 1)² (x⁻¹)^A)` for a single `A`-independent constant `K₀ ≥ 0`; since `0 ≤ x⁻¹ < 1`
(from `x > 1`), `General.tendsto_add_one_pow_mul_pow_of_lt_one` (the polynomial × geometric decay
squeeze) gives `(A + 1)² (x⁻¹)^A → 0`, and `squeeze_zero_norm`
finishes.
Role: **the left-edge completion theorem** — the fixed-`A` left-vertical edge integral vanishes as
the
contour's left edge is pushed to `-∞`, matching the horizontal argument's horizontal-edge vanishing
and the height-selection argument's central
identification to close the primitive explicit-formula contour on the left.
-/
theorem quadraticTendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun A : ℕ ↦
        ∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  obtain ⟨D, hDnn, hD⟩ :=
    exists_C_norm_logDeriv_dirichletLFunction_leftVertical_le
      hprimitive hne hquad
  have hMassnn : (0 : ℝ) ≤ General.logQuadraticEnvelopeMass :=
    General.logQuadraticEnvelopeMass_nonneg
  set r : ℝ := x⁻¹ with hr_def
  have hr0 : (0 : ℝ) ≤ r := by
    rw [hr_def]; positivity
  have hr1 : r < 1 := by
    rw [hr_def]; exact inv_lt_one_of_one_lt₀ hx
  have hxpow_split : ∀ A : ℕ, x ^ (-(A : ℝ) - 3 / 2) = x ^ (-(3 : ℝ) / 2) * r ^ A := by
    intro A
    rw [hr_def, show -(A : ℝ) - 3 / 2 = -(3 : ℝ) / 2 + -(A : ℝ) from by ring, Real.rpow_add hxpos,
      Real.rpow_neg hxpos.le, Real.rpow_natCast, ← inv_pow]
  have hpoly_le : ∀ A : ℕ, ((A : ℝ) + 5) ^ 2 + 1 ≤ 26 * (((A : ℝ) + 1) ^ 2) := by
    intro A
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    nlinarith [sq_nonneg (A : ℝ)]
  set K : ℝ :=
    D * x ^ (-(3 : ℝ) / 2) * General.logQuadraticEnvelopeMass *
      26 with
    hK_def
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK_def]; positivity
  have hbound :
    ∀ A : ℕ,
      2 ≤ A →
        ‖∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          K * (((A : ℝ) + 1) ^ 2 * r ^ A) := by
    intro A hA
    have hI :=
      norm_integral_dirichletReciprocalContourKernel_leftVertical_of_bound
        hxpos hA hDnn (fun t => hD A hA t)
    have hxApow_nn : (0 : ℝ) ≤ x ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos hxpos _ |>.le
    have hrApow_nn : (0 : ℝ) ≤ r ^ A := by positivity
    calc
      ‖∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          D * x ^ (-(A : ℝ) - 3 / 2) * (((A : ℝ) + 5) ^ 2 + 1) *
            General.logQuadraticEnvelopeMass :=
        hI
      _ =
          D * (x ^ (-(3 : ℝ) / 2) * r ^ A) * (((A : ℝ) + 5) ^ 2 + 1) *
            General.logQuadraticEnvelopeMass :=
        by rw [hxpow_split A]
      _ ≤
          D * (x ^ (-(3 : ℝ) / 2) * r ^ A) * (26 * (((A : ℝ) + 1) ^ 2)) *
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
