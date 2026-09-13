/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFarLeftHorizontalBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveCentralHorizontalBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HeightRectangle
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge

/-!
# Horizontal logarithmic-kernel bounds for quadratic characters

Logarithmic-kernel analogue of the horizontal argument's central/far-left horizontal pointwise
bounds and their
`k → ∞` vanishing, mirroring the central reciprocal-kernel theorems and
the corresponding horizontal-merge step. All the `L'/L` growth
ingredients (`DirichletLFunction.exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small`,
`exists_norm_logDeriv_dirichletLFunction_farLeft_le`) are kernel-independent and reused as-is; only
the kernel-specific pointwise wrapping changes, replacing the reciprocal kernel's `x^(s-1)/(s(s-1))`
shape by the log kernel's `x^s/s²` shape — concretely, the power-of-`x` exponent loses its `- 1`
shift (central strip `|σ| ≤ 2` bound becomes `x²` instead of `x`), and the denominator lower bound
uses `‖s‖²` directly instead of `‖s‖ * ‖s - 1‖`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The log kernel's central-strip pointwise bound -/

/--
Input/assumptions: `x ≥ 1`, `|σ| ≤ 2`, `T ≠ 0`, and a bound
`‖logDeriv (LFunction χ) (σ + T i)‖ / T² ≤ η` on the ordinary log-derivative.
Conclusion: `‖DirichletLFunction.dirichletLogContourKernel x χ (σ + T i)‖ ≤ x² * η`.
Content: `‖x ^ s‖ = x ^ σ ≤ x ^ 2` (`Complex.norm_cpow_eq_rpow_re_of_pos` +
`Real.rpow_le_rpow_of_exponent_le`, since `σ ≤ 2` from `|σ| ≤ 2`); `T² ≤ ‖s‖²`
(`Complex.abs_im_le_norm`); the kernel unfolds to `‖logDeriv (LFunction χ) s‖ * ‖x ^ s‖ / ‖s‖²`, so
combining the two bounds and the numerator hypothesis `hL` gives `≤ x² * η`.
Role: the log-kernel central `[-2, 2]` and fixed-`A` far-left horizontal integral bound ingredient.
-/
private theorem quadraticNorm_dirichletLogContourKernel_horizontal_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : |σ| ≤ 2) (hT : T ≠ 0)
    (hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletLogContourKernel x χ
          ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      x ^ 2 * η := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsre : s.re = σ := by
    simp only [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxs : ‖(x : ℂ) ^ s‖ = x ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsre]
  have hxσpos : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hxpos σ
  have hxσ_le : x ^ σ ≤ x ^ 2 := by
    have h1 : x ^ σ ≤ x ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx
        (by
          have := abs_le.mp hσ; linarith)
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num only, Real.rpow_natCast] at h1
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
  have h1 :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ ≤
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ 2 :=
    mul_le_mul_of_nonneg_left hxσ_le (norm_nonneg _)
  have h2 : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ := by positivity
  have h3 : T ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← sq_abs T]; exact pow_le_pow_left₀ htabs_pos.le hsnorm_ge 2
  have hTsq_pos : (0 : ℝ) < T ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ ^ 2 ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / T ^ 2 :=
      div_le_div_of_nonneg_left h2 hTsq_pos h3
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ 2 / T ^ 2 :=
      div_le_div_of_nonneg_right h1 hTsq_pos.le
    _ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ / T ^ 2 * x ^ 2 := by ring
    _ ≤ η * x ^ 2 := by apply mul_le_mul_of_nonneg_right hL (by positivity)
    _ = x ^ 2 * η := by ring

/--
Input/assumptions: `N ≥ 2`, `χ` primitive quadratic non-principal mod `N` with `χ⁻¹ ≠ 1`, GRH,
`x ≥ 1`.
Conclusion: there is an envelope `η : ℕ → ℝ → 0` such that for every `k` and every `σ` with
`|σ| ≤ 2`, `‖DirichletLFunction.dirichletLogContourKernel x χ (σ ± i
(DirichletLFunction.primitiveHorizontalHeightSeq k))‖ ≤ x² * η k`.
Content: combines `DirichletLFunction.exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small`
(kernel-independent, reused as-is) with the generic
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.norm_dirichletLogContourKernel_horizontal_le`.
Role: feeds the central horizontal integral bound below.
-/
theorem exists_primitiveHorizontalHeightSeq_logKernel_bound
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 →
              ‖dirichletLogContourKernel x χ
                      ((σ : ℂ) +
                        primitiveHorizontalHeightSeq
                            hN2 hGRH hprimitive hne hinv hquad k *
                          Complex.I)‖ ≤
                  x ^ 2 * η k ∧
                ‖dirichletLogContourKernel x χ
                      ((σ : ℂ) -
                        primitiveHorizontalHeightSeq
                            hN2 hGRH hprimitive hne hinv hquad k *
                          Complex.I)‖ ≤
                  x ^ 2 * η k := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small
      hN2 hGRH hprimitive hne hinv hquad
  refine ⟨η, hη_tendsto, fun k σ hσ => ?_⟩
  set T : ℕ → ℝ :=
    primitiveHorizontalHeightSeq hN2 hGRH
      hprimitive hne hinv hquad with
    hT_def
  have hTk_ge1 : 1 ≤ T k := by
    have h :=
      primitiveHorizontalHeightSeq_ge hN2 hGRH
        hprimitive hne hinv hquad k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hT_def]; linarith
  have hTk_ne : T k ≠ 0 := by linarith
  refine
    ⟨quadraticNorm_dirichletLogContourKernel_horizontal_le
        hx hσ hTk_ne (hη k σ hσ).1,
      ?_⟩
  have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hform]
  have hL2 := (hη k σ hσ).2
  rw [hform, ← neg_sq] at hL2
  exact
    quadraticNorm_dirichletLogContourKernel_horizontal_le
      hx hσ (neg_ne_zero.mpr hTk_ne) hL2

/-- A common envelope `η k → 0` bounds both central logarithmic integrals by `4*x²*η k`.
Integrate the pointwise quadratic-character bound over `[-2,2]`. -/
theorem exists_primitiveHorizontalHeightSeq_logKernel_central_integral_le
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-2 : ℝ)..2,
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq
                          hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              4 * (x ^ 2 * η k) ∧
            ‖∫ σ in (-2 : ℝ)..2,
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq
                          hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              4 * (x ^ 2 * η k) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_logKernel_bound
      hN2 hGRH hprimitive hne hinv hquad hx
  refine ⟨η, hη_tendsto, fun k => ⟨?_, ?_⟩⟩
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletLogContourKernel x χ
          ((σ : ℂ) +
            primitiveHorizontalHeightSeq hN2
                hGRH hprimitive hne hinv hquad k *
              Complex.I))
        (C := x ^ 2 * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).1)
    rw [show |(2 : ℝ) - (-2)| = 4 from by norm_num only] at hbound
    linarith
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletLogContourKernel x χ
          ((σ : ℂ) -
            primitiveHorizontalHeightSeq hN2
                hGRH hprimitive hne hinv hquad k *
              Complex.I))
        (C := x ^ 2 * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).2)
    rw [show |(2 : ℝ) - (-2)| = 4 from by norm_num only] at hbound
    linarith

/-- Both central logarithmic integrals tend to zero along the quadratic-character heights,
by squeezing their norms with the preceding envelope. -/
theorem tendsto_primitiveHorizontalHeightSeq_logKernel_central_integral
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_logKernel_central_integral_le
      hN2 hGRH hprimitive hne hinv hquad hx
  have htend : Filter.Tendsto (fun k : ℕ => 4 * (x ^ 2 * η k)) Filter.atTop (nhds 0) := by
    have := hη_tendsto.const_mul (4 * x ^ 2)
    simpa only [mul_assoc, mul_zero] using this
  exact ⟨squeeze_zero_norm (fun k => (hη k).1) htend, squeeze_zero_norm (fun k => (hη k).2) htend⟩

/-! ### The log kernel's far-left pointwise bound -/

/--
Input/assumptions: `x ≥ 1`, `σ ≤ -2`, `T ≠ 0`, and a bound `‖logDeriv (LFunction χ) (σ + T i)‖ /
T² ≤ η`.
Conclusion: `‖DirichletLFunction.dirichletLogContourKernel x χ (σ + T i)‖ ≤ η`.
Content: same structure as `DirichletLFunction.norm_dirichletReciprocalContourKernel_farLeft_le`,
except
`‖x ^ s‖ = x ^ σ ≤ x ^ (-2) ≤ 1` (`σ ≤ -2` and `x ≥ 1`), so the numerator bound is `η * T²` rather
than `η * T² * x`.
Role: the log-kernel far-left pointwise ingredient.
-/
private theorem quadraticNorm_dirichletLogContourKernel_farLeft_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ -2) (hT : T ≠ 0)
    (hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletLogContourKernel x χ
          ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      η := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsre : s.re = σ := by
    simp only [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxs : ‖(x : ℂ) ^ s‖ = x ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsre]
  have hxσpos : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hxpos σ
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
  have h1 :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ ≤
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * 1 :=
    mul_le_mul_of_nonneg_left hxσ_le (norm_nonneg _)
  have h2 : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ := by positivity
  have h3 : T ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← sq_abs T]; exact pow_le_pow_left₀ htabs_pos.le hsnorm_ge 2
  have hTsq_pos : (0 : ℝ) < T ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / ‖s‖ ^ 2 ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ σ / T ^ 2 :=
      div_le_div_of_nonneg_left h2 hTsq_pos h3
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * 1 / T ^ 2 :=
      div_le_div_of_nonneg_right h1 hTsq_pos.le
    _ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ / T ^ 2 := by ring
    _ ≤ η := hL

/-- For fixed `A ≥ 2`, a common envelope tending to zero bounds both far-left logarithmic
integrals along the quadratic-character heights. Integrate the far-left pointwise bound. -/
theorem exists_primitiveHorizontalHeightSeq_logKernel_farLeft_integral_le
    (A : ℕ) (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ μ : ℕ → ℝ,
      Filter.Tendsto μ Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq
                          hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              μ k ∧
            ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq
                          hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              μ k := by
  have hAab : -(A : ℝ) - 1 / 2 ≤ -2 := by
    have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  obtain ⟨D, hDnonneg, hD⟩ :=
    exists_norm_logDeriv_dirichletLFunction_farLeft_le
      A hprimitive hne hquad
  set T : ℕ → ℝ :=
    primitiveHorizontalHeightSeq hN2 hGRH
      hprimitive hne hinv hquad with
    hT_def
  have hT_tendsto : Filter.Tendsto T Filter.atTop Filter.atTop :=
    tendsto_primitiveHorizontalHeightSeq_atTop
      hN2 hGRH hprimitive hne hinv hquad
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
      have h :=
        primitiveHorizontalHeightSeq_ge hN2 hGRH
          hprimitive hne hinv hquad k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]; linarith
    have hTk_pos : (0 : ℝ) < T k := by linarith
    have hTksq_pos : (0 : ℝ) < (T k) ^ 2 := by positivity
    have hTk_ne : T k ≠ 0 := by linarith
    have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-(A : ℝ) - 1 / 2)) (b := -2) (f :=
        fun σ : ℝ =>
        dirichletLogContourKernel x χ
          ((σ : ℂ) + T k * Complex.I))
        (C := η k)
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
            rw [hη_def]; exact div_le_div_of_nonneg_right hLbase hTksq_pos.le
          exact
            quadraticNorm_dirichletLogContourKernel_farLeft_le
              hx hσ2 hTk_ne hL')
    rwa [hμ_def, hL_def]
  · have hTk_ge1 : 1 ≤ T k := by
      have h :=
        primitiveHorizontalHeightSeq_ge hN2 hGRH
          hprimitive hne hinv hquad k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]; linarith
    have hTk_pos : (0 : ℝ) < T k := by linarith
    have hTksq_pos : (0 : ℝ) < (T k) ^ 2 := by positivity
    have hTk_ne : T k ≠ 0 := by linarith
    have hform :
      ∀ σ : ℝ, (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I :=
      fun σ => by
      push_cast; ring
    have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-(A : ℝ) - 1 / 2)) (b := -2) (f :=
        fun σ : ℝ =>
        dirichletLogContourKernel x χ
          ((σ : ℂ) - T k * Complex.I))
        (C := η k)
        (by
          rintro σ hσ
          rw [Set.uIoc_of_le hAab] at hσ
          obtain ⟨hσ1, hσ2⟩ := hσ
          rw [hform σ]
          have hTk_abs : (1 : ℝ) ≤ |-(T k)| := by
            rw [abs_neg, abs_of_nonneg hTk_pos.le]; exact hTk_ge1
          have hLbase := hD σ (-(T k)) hσ1.le hσ2 hTk_abs
          rw [abs_neg, abs_of_nonneg hTk_pos.le] at hLbase
          have hL2' :
            ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I)‖ /
                (-(T k)) ^ 2 ≤
              η k := by
            rw [neg_sq, hη_def]
            exact div_le_div_of_nonneg_right hLbase hTksq_pos.le
          exact
            quadraticNorm_dirichletLogContourKernel_farLeft_le
              hx hσ2 (neg_ne_zero.mpr hTk_ne) hL2')
    rwa [hμ_def, hL_def]

/-- Both far-left logarithmic integrals tend to zero for fixed `A ≥ 2`, by squeezing
with the common envelope along the quadratic-character heights. -/
theorem tendsto_primitiveHorizontalHeightSeq_logKernel_farLeft_integral
    (A : ℕ) (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨μ, hμ_tendsto, hμ⟩ :=
    exists_primitiveHorizontalHeightSeq_logKernel_farLeft_integral_le
      A hA hN2 hGRH hprimitive hne hinv hquad hx
  exact
    ⟨squeeze_zero_norm (fun k => (hμ k).1) hμ_tendsto,
      squeeze_zero_norm (fun k => (hμ k).2) hμ_tendsto⟩

/-! ### The merged horizontal-edge vanishing, log kernel -/

/-- Log-kernel analogue of
`DirichletLFunction.continuous_dirichletReciprocalContourKernel_horizontalHeightSeq`. -/
theorem continuous_dirichletLogContourKernel_horizontalHeightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (k : ℕ) :
    Continuous
        (fun σ : ℝ =>
          dirichletLogContourKernel x χ
            ((σ : ℂ) +
              primitiveHorizontalHeightSeq hN2
                  hGRH hprimitive hne hinv hquad k *
                Complex.I)) ∧
      Continuous
        (fun σ : ℝ =>
          dirichletLogContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq hN2
                  hGRH hprimitive hne hinv hquad k *
                Complex.I)) := by
  have hTge :=
    primitiveHorizontalHeightSeq_ge hN2 hGRH
      hprimitive hne hinv hquad k
  have hTpos :
    (0 : ℝ) <
      primitiveHorizontalHeightSeq hN2 hGRH
        hprimitive hne hinv hquad k := by
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hpt :
    ∀ s : ℂ,
      s.im =
            primitiveHorizontalHeightSeq hN2
              hGRH hprimitive hne hinv hquad k ∨
          s.im =
            -(primitiveHorizontalHeightSeq hN2
                hGRH hprimitive hne hinv hquad k) →
        ContinuousAt
          (dirichletLogContourKernel x χ)
          s := by
    intro s hsim
    have hsimne : s.im ≠ 0 := by
      rcases hsim with h | h <;> rw [h] <;> [exact hTpos.ne'; exact (neg_lt_zero.mpr hTpos).ne]
    have hs0 : s ≠ 0 := fun h =>
      hsimne
        (by
          rw [h]; simp only [Complex.zero_im])
    have hLne :=
      dirichletLFunction_ne_zero_of_im_eq_primitiveHorizontalHeightSeq
        hN2 hGRH hprimitive hne hinv hquad k hsim
    exact
      (differentiableAt_dirichletLogContourKernel
          hx hne hs0 hLne).continuousAt
  constructor
  · have hg :
      Continuous
        (fun σ : ℝ =>
          (σ : ℂ) +
            (primitiveHorizontalHeightSeq hN2
                  hGRH hprimitive hne hinv hquad k :
                ℂ) *
              Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn
        (dirichletLogContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) +
              (primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k :
                  ℂ) *
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
            (primitiveHorizontalHeightSeq hN2
                  hGRH hprimitive hne hinv hquad k :
                ℂ) *
              Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn
        (dirichletLogContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) -
              (primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k :
                  ℂ) *
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

/-- Both full horizontal logarithmic integrals tend to zero for fixed `A ≥ 2`.
Continuity permits splitting at `-2`; add the central and far-left limits. -/
theorem tendsto_primitiveHorizontalHeightSeq_logKernel_horizontal_integral
    (A : ℕ) (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hfarLeft :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_farLeft_integral
      A hA hN2 hGRH hprimitive hne hinv hquad hx
  have hcentral :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_central_integral
      hN2 hGRH hprimitive hne hinv hquad hx
  have hcont := fun k : ℕ =>
    continuous_dirichletLogContourKernel_horizontalHeightSeq
      hN2 hGRH hprimitive hne hinv hquad hxpos k
  have hsplit :
    ∀ k : ℕ,
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I)) +
          ∫ σ in (-2 : ℝ)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
          dirichletLogContourKernel x χ
            ((σ : ℂ) +
              primitiveHorizontalHeightSeq hN2
                  hGRH hprimitive hne hinv hquad k *
                Complex.I) :=
    fun k =>
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont k).1.intervalIntegrable (-(A : ℝ) - 1 / 2) (-2))
      ((hcont k).1.intervalIntegrable (-2) 2)
  have hsplit' :
    ∀ k : ℕ,
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I)) +
          ∫ σ in (-2 : ℝ)..(2 : ℝ),
            dirichletLogContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
          dirichletLogContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq hN2
                  hGRH hprimitive hne hinv hquad k *
                Complex.I) :=
    fun k =>
    intervalIntegral.integral_add_adjacent_intervals
      ((hcont k).2.intervalIntegrable (-(A : ℝ) - 1 / 2) (-2))
      ((hcont k).2.intervalIntegrable (-2) 2)
  constructor
  · have := (hfarLeft.1.add hcentral.1)
    simp only [add_zero] at this
    exact this.congr hsplit
  · have := (hfarLeft.2.add hcentral.2)
    simp only [add_zero] at this
    exact this.congr hsplit'

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
