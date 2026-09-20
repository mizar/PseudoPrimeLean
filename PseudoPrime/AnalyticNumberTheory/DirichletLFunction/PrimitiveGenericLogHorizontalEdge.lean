/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFarLeftHorizontalBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HeightRectangle
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveOrdinaryLogDerivBound

/-! Generic logarithmic horizontal-edge estimates and their height-sequence limits. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `x ≥ 1`, `|σ| ≤ 2`, `T ≠ 0`, and a bound on the ordinary logarithmic
derivative at `σ + T i` divided by `T²`.
Conclusion: the logarithmic contour kernel is bounded by `x²` times that envelope.
Content: the positive-base complex-power norm is bounded by `x²`; the imaginary part controls
the denominator `‖s‖²`, so the kernel-specific estimate is independent of character parity.
Role: central-strip pointwise input for the generic logarithmic horizontal edge.
-/
theorem norm_dirichletLogContourKernel_horizontal_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : |σ| ≤ 2) (hT : T ≠ 0)
    (hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletLogContourKernel x χ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ x ^ 2 * η := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsre : s.re = σ := by
    simp only [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxs : ‖(x : ℂ) ^ s‖ = x ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsre]
  have hxσ_le : x ^ σ ≤ x ^ 2 := by
    have h1 : x ^ σ ≤ x ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx
        (by
          have := abs_le.mp hσ
          linarith)
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] at h1
  have htabs_pos : (0 : ℝ) < |T| := abs_pos.mpr hT
  have hsnorm_ge : |T| ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rwa [hsim] at h
  have hK_eq :
    ‖dirichletLogContourKernel x χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ ^ 2 := by
    have hlogDeriv_eq :
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [logDeriv_apply]
    unfold dirichletLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hxs, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have hnum :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ ≤
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ 2 :=
    mul_le_mul_of_nonneg_left hxσ_le (norm_nonneg _)
  have hnum_nonneg : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ := by
    positivity
  have hden : T ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← sq_abs T]
    exact pow_le_pow_left₀ htabs_pos.le hsnorm_ge 2
  have hT2_pos : (0 : ℝ) < T ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ ^ 2 ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / T ^ 2 :=
      div_le_div_of_nonneg_left hnum_nonneg hT2_pos hden
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ 2 / T ^ 2 :=
      div_le_div_of_nonneg_right hnum hT2_pos.le
    _ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ / T ^ 2 * x ^ 2 := by ring
    _ ≤ η * x ^ 2 := by exact mul_le_mul_of_nonneg_right hL (by positivity)
    _ = x ^ 2 * η := by ring

/--
Input/assumptions: `N ≥ 2`, a primitive nontrivial character with nontrivial inverse, GRH,
and `x ≥ 1`.
Conclusion: along the generic good-height sequence, both horizontal logarithmic kernels have a
common bound `x² * η k`, where `η k → 0` already includes the height-square division.
Content: applies the `hquad`-free ordinary logarithmic-derivative envelope to the pointwise kernel
bound above, using the same positive and negative heights as the contour API.
Role: supplies the central horizontal integral estimate used by the generic log contour limit.
-/
theorem exists_primitiveHorizontalHeightSeq_logKernel_bound_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 →
              ‖dirichletLogContourKernel x χ
                      ((σ : ℂ) +
                        primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                          Complex.I)‖ ≤
                  x ^ 2 * η k ∧
                ‖dirichletLogContourKernel x χ
                      ((σ : ℂ) -
                        primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                          Complex.I)‖ ≤
                  x ^ 2 * η k := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small_of_grh hN2 hGRH hprimitive hne hinv
  refine ⟨η, hη_tendsto, fun k σ hσ => ?_⟩
  have hTk_ge1 : 1 ≤ primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k := by
    have h := primitiveHorizontalHeightSeq_ge_of_grh hN2 hGRH hprimitive hne hinv k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hTk_ne : primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k ≠ 0 := by
    linarith
  refine ⟨norm_dirichletLogContourKernel_horizontal_le hx hσ hTk_ne (hη k σ hσ).1, ?_⟩
  have hform :
    (σ : ℂ) - primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I =
      (σ : ℂ) +
        (-(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k) : ℝ) *
          Complex.I := by
    push_cast
    ring
  rw [hform]
  have hL2 := (hη k σ hσ).2
  rw [hform, ← neg_sq] at hL2
  exact norm_dirichletLogContourKernel_horizontal_le hx hσ (neg_ne_zero.mpr hTk_ne) hL2

/--
Input/assumptions: the hypotheses of
`DirichletLFunction.exists_primitiveHorizontalHeightSeq_logKernel_bound_of_grh`.
Conclusion: each central horizontal interval integral is bounded by `4 * x² * η k` for an
envelope `η → 0`.
Content: integrate the pointwise bound on `[-2, 2]` with the standard interval-integral norm
estimate; the same envelope controls both orientations.
Role: the central component of the generic logarithmic horizontal-edge vanishing theorem.
-/
theorem exists_primitiveHorizontalHeightSeq_logKernel_central_integral_le_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-2 : ℝ)..2,
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              4 * (x ^ 2 * η k) ∧
            ‖∫ σ in (-2 : ℝ)..2,
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              4 * (x ^ 2 * η k) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_logKernel_bound_of_grh hN2 hGRH hprimitive hne hinv hx
  refine ⟨η, hη_tendsto, fun k => ⟨?_, ?_⟩⟩
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletLogContourKernel x χ
          ((σ : ℂ) +
            primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        (C := x ^ 2 * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).1)
    rw [show |(2 : ℝ) - (-2)| = 4 by norm_num only] at hbound
    linarith
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletLogContourKernel x χ
          ((σ : ℂ) -
            primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        (C := x ^ 2 * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).2)
    rw [show |(2 : ℝ) - (-2)| = 4 by norm_num only] at hbound
    linarith

/-- The generic central horizontal logarithmic integrals converge to zero along GRH heights. -/
theorem tendsto_primitiveHorizontalHeightSeq_logKernel_central_integral_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_logKernel_central_integral_le_of_grh hN2 hGRH hprimitive hne
      hinv hx
  have htend : Filter.Tendsto (fun k : ℕ => 4 * (x ^ 2 * η k)) Filter.atTop (nhds 0) := by
    have h := hη_tendsto.const_mul (4 * x ^ 2)
    simpa only [mul_assoc, mul_zero] using h
  exact ⟨squeeze_zero_norm (fun k => (hη k).1) htend, squeeze_zero_norm (fun k => (hη k).2) htend⟩

/--
Input/assumptions: `x ≥ 1`, `σ ≤ -2`, `T ≠ 0`, and an ordinary logarithmic-derivative bound
divided by `T²`.
Conclusion: the logarithmic contour kernel is bounded by the same envelope on the far-left strip.
Content: `x^σ ≤ 1` for `x ≥ 1` and `σ ≤ -2`; the denominator is controlled by the imaginary part.
Role: pointwise input for the generic far-left horizontal integral.
-/
theorem norm_dirichletLogContourKernel_farLeft_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ -2) (hT : T ≠ 0)
    (hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletLogContourKernel x χ ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤ η := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsre : s.re = σ := by
    simp only [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxs : ‖(x : ℂ) ^ s‖ = x ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsre]
  have hxσ_le : x ^ σ ≤ 1 := by
    have h1 : x ^ σ ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rwa [Real.rpow_zero] at h1
  have htabs_pos : (0 : ℝ) < |T| := abs_pos.mpr hT
  have hsnorm_ge : |T| ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rwa [hsim] at h
  have hK_eq :
    ‖dirichletLogContourKernel x χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ ^ 2 := by
    have hlogDeriv_eq :
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [logDeriv_apply]
    unfold dirichletLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hxs, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have hnum :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ ≤
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * 1 :=
    mul_le_mul_of_nonneg_left hxσ_le (norm_nonneg _)
  have hnum_nonneg : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ := by
    positivity
  have hden : T ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← sq_abs T]
    exact pow_le_pow_left₀ htabs_pos.le hsnorm_ge 2
  have hT2_pos : (0 : ℝ) < T ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ ^ 2 ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / T ^ 2 :=
      div_le_div_of_nonneg_left hnum_nonneg hT2_pos hden
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * 1 / T ^ 2 :=
      div_le_div_of_nonneg_right hnum hT2_pos.le
    _ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ / T ^ 2 := by ring
    _ ≤ η := hL

/--
Input/assumptions: `A ≥ 2`, `N ≥ 2`, a primitive nontrivial character with nontrivial inverse,
GRH, and `x ≥ 1`.
Conclusion: a common envelope `μ k → 0` bounds the norms of both fixed-`A` far-left
logarithmic horizontal integrals along the generic good-height sequence.
Content: the generic far-left logarithmic-derivative envelope is integrated over the fixed segment;
its `(T+1)/T²` factor tends to zero.
Role: far-left component of the generic logarithmic horizontal-edge limit.
-/
theorem exists_primitiveHorizontalHeightSeq_logKernel_farLeft_integral_le_of_grh (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ μ : ℕ → ℝ,
      Filter.Tendsto μ Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              μ k ∧
            ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              μ k := by
  have hAab : -(A : ℝ) - 1 / 2 ≤ -2 := by
    have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  obtain ⟨D, hDnonneg, hD⟩ :=
    exists_norm_logDeriv_dirichletLFunction_farLeft_le_general A hprimitive hne hinv
  set T : ℕ → ℝ := primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv with hT_def
  have hT_tendsto : Filter.Tendsto T Filter.atTop Filter.atTop :=
    tendsto_primitiveHorizontalHeightSeq_atTop_of_grh hN2 hGRH hprimitive hne hinv
  set η : ℕ → ℝ := fun k => D * (T k + 1) / (T k) ^ 2 with hη_def
  set L : ℝ := |(-2 : ℝ) - (-(A : ℝ) - 1 / 2)| with hL_def
  set μ : ℕ → ℝ := fun k => η k * L with hμ_def
  have hη_tendsto : Filter.Tendsto η Filter.atTop (nhds 0) := by
    have h2D_tendsto : Filter.Tendsto (fun k : ℕ => 2 * D / T k) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hT_tendsto
    have hupper : ∀ᶠ k : ℕ in Filter.atTop, η k ≤ 2 * D / T k := by
      filter_upwards [hT_tendsto.eventually_ge_atTop (1 : ℝ)] with k hk
      have hTk_pos : 0 < T k := by linarith
      rw [hη_def, div_le_div_iff₀ (by positivity) hTk_pos]
      have h1 : D * (T k + 1) ≤ D * (2 * T k) := by nlinarith [hDnonneg, hk]
      nlinarith [h1]
    have hlower : ∀ᶠ k : ℕ in Filter.atTop, (0 : ℝ) ≤ η k := by
      filter_upwards [hT_tendsto.eventually_gt_atTop (0 : ℝ)] with k hk
      exact div_nonneg (mul_nonneg hDnonneg (by linarith)) (by positivity)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2D_tendsto hlower hupper
  refine ⟨μ, by simpa only [hμ_def, zero_mul] using hη_tendsto.mul_const L, fun k => ⟨?_, ?_⟩⟩
  · have hTk_ge1 : 1 ≤ T k := by
      have h := primitiveHorizontalHeightSeq_ge_of_grh hN2 hGRH hprimitive hne hinv k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]
      linarith
    have hTk_pos : 0 < T k := by linarith
    have hTksq_pos : 0 < (T k) ^ 2 := by positivity
    have hTk_ne : T k ≠ 0 := by linarith
    have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-(A : ℝ) - 1 / 2)) (b := -2) (f :=
        fun σ : ℝ => dirichletLogContourKernel x χ ((σ : ℂ) + T k * Complex.I)) (C := η k)
        (by
          rintro σ hσ
          rw [Set.uIoc_of_le hAab] at hσ
          obtain ⟨hσ1, hσ2⟩ := hσ
          have hLbase :=
            hD σ (T k) hσ1.le hσ2
              (by
                rw [abs_of_nonneg hTk_pos.le]; exact hTk_ge1)
          rw [abs_of_nonneg hTk_pos.le] at hLbase
          have hL' :
            ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T k * Complex.I)‖ / (T k) ^ 2 ≤
              η k := by
            rw [hη_def]
            exact div_le_div_of_nonneg_right hLbase hTksq_pos.le
          exact norm_dirichletLogContourKernel_farLeft_le hx hσ2 hTk_ne hL')
    rwa [hμ_def, hL_def]
  · have hTk_ge1 : 1 ≤ T k := by
      have h := primitiveHorizontalHeightSeq_ge_of_grh hN2 hGRH hprimitive hne hinv k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]
      linarith
    have hTk_pos : 0 < T k := by linarith
    have hTksq_pos : 0 < (T k) ^ 2 := by positivity
    have hTk_ne : T k ≠ 0 := by linarith
    have hform :
      ∀ σ : ℝ, (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I :=
      fun σ => by
      push_cast
      ring
    have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-(A : ℝ) - 1 / 2)) (b := -2) (f :=
        fun σ : ℝ => dirichletLogContourKernel x χ ((σ : ℂ) - T k * Complex.I)) (C := η k)
        (by
          rintro σ hσ
          rw [Set.uIoc_of_le hAab] at hσ
          obtain ⟨hσ1, hσ2⟩ := hσ
          rw [hform σ]
          have hTk_abs : (1 : ℝ) ≤ |-(T k)| := by
            rw [abs_neg, abs_of_nonneg hTk_pos.le]
            exact hTk_ge1
          have hLbase := hD σ (-(T k)) hσ1.le hσ2 hTk_abs
          rw [abs_neg, abs_of_nonneg hTk_pos.le] at hLbase
          have hL2' :
            ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I)‖ /
                (-(T k)) ^ 2 ≤
              η k := by
            rw [neg_sq, hη_def]
            exact div_le_div_of_nonneg_right hLbase hTksq_pos.le
          exact norm_dirichletLogContourKernel_farLeft_le hx hσ2 (neg_ne_zero.mpr hTk_ne) hL2')
    rwa [hμ_def, hL_def]

/-- The generic far-left logarithmic horizontal integrals converge to zero along the GRH heights. -/
theorem tendsto_primitiveHorizontalHeightSeq_logKernel_farLeft_integral_of_grh (A : ℕ) (hA : 2 ≤ A)
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨μ, hμ_tendsto, hμ⟩ :=
    exists_primitiveHorizontalHeightSeq_logKernel_farLeft_integral_le_of_grh A hA hN2 hGRH
      hprimitive hne hinv hx
  exact
    ⟨squeeze_zero_norm (fun k => (hμ k).1) hμ_tendsto,
      squeeze_zero_norm (fun k => (hμ k).2) hμ_tendsto⟩

/-- The generic logarithmic kernel is continuous on each GRH horizontal height line. -/
theorem continuous_dirichletLogContourKernel_horizontalHeightSeq_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Continuous
        (fun σ : ℝ =>
          dirichletLogContourKernel x χ
            ((σ : ℂ) +
              primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I)) ∧
      Continuous
        (fun σ : ℝ =>
          dirichletLogContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I)) := by
  have hTge := primitiveHorizontalHeightSeq_ge_of_grh hN2 hGRH hprimitive hne hinv k
  have hTpos : (0 : ℝ) < primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpt :
    ∀ s : ℂ,
      s.im = primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k ∨
          s.im = -(primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k) →
        ContinuousAt (dirichletLogContourKernel x χ) s := by
    intro s hsim
    have hsimne : s.im ≠ 0 := by
      rcases hsim with h | h
      · rw [h]
        exact hTpos.ne'
      · rw [h]
        exact (neg_lt_zero.mpr hTpos).ne
    have hs0 : s ≠ 0 := fun h =>
      hsimne
        (by
          rw [h]; simp only [Complex.zero_im])
    have hLne :=
      dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k
        hsim
    exact (differentiableAt_dirichletLogContourKernel hx hne hs0 hLne).continuousAt
  constructor
  · have hg :
      Continuous
        (fun σ : ℝ =>
          (σ : ℂ) +
            (primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k : ℂ) *
              Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn (dirichletLogContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) +
              (primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k : ℂ) *
                Complex.I)) := by
      rintro s ⟨σ, rfl⟩
      exact
        (hpt _
            (Or.inl
              (by
                simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
                  zero_add]))).continuousWithinAt
    exact hOn.comp_continuous hg (fun σ => Set.mem_range_self σ)
  · have hg :
      Continuous
        (fun σ : ℝ =>
          (σ : ℂ) -
            (primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k : ℂ) *
              Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn (dirichletLogContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) -
              (primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k : ℂ) *
                Complex.I)) := by
      rintro s ⟨σ, rfl⟩
      exact
        (hpt _
            (Or.inr
              (by
                simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
                  zero_sub]))).continuousWithinAt
    exact hOn.comp_continuous hg (fun σ => Set.mem_range_self σ)

/--
Under the primitive-character GRH hypotheses, with `A ≥ 2` and `x ≥ 1`, both full
horizontal logarithmic-kernel integrals tend to zero. Split each integral at `-2`,
using continuity for interval integrability, then add the far-left and central limits.
-/
theorem tendsto_primitiveHorizontalHeightSeq_logKernel_horizontal_integral_of_grh (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hfarLeft :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_farLeft_integral_of_grh A hA hN2 hGRH hprimitive
      hne hinv hx
  have hcentral :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_central_integral_of_grh hN2 hGRH hprimitive hne
      hinv hx
  have hcont := fun k : ℕ =>
    continuous_dirichletLogContourKernel_horizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv
      hxpos k
  have hsplit :
    ∀ k : ℕ,
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I)) +
          ∫ σ in (-2 : ℝ)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
          dirichletLogContourKernel x χ
            ((σ : ℂ) +
              primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I) :=
    fun k =>
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont k).1.intervalIntegrable (-(A : ℝ) - 1 / 2) (-2))
      ((hcont k).1.intervalIntegrable (-2) 2)
  have hsplit' :
    ∀ k : ℕ,
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I)) +
          ∫ σ in (-2 : ℝ)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
          dirichletLogContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I) :=
    fun k =>
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont k).2.intervalIntegrable (-(A : ℝ) - 1 / 2) (-2))
      ((hcont k).2.intervalIntegrable (-2) 2)
  constructor
  · have h := hfarLeft.1.add hcentral.1
    simp only [add_zero] at h
    exact h.congr (hsplit)
  · have h := hfarLeft.2.add hcentral.2
    simp only [add_zero] at h
    exact h.congr (hsplit')

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
