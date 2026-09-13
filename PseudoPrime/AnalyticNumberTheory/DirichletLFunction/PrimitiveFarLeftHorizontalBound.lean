/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveCentralHorizontalBound
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HorizontalFarLeftBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorGrowth
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FarLeftReflection

/-!
# Far-left horizontal reciprocal-kernel integrals vanish

The reflection estimates in `FarLeftReflection` bound the ordinary logarithmic derivative
on the fixed strip `[-A-1/2,-2]` by `O_A(|T|+1)`. The reciprocal Mellin factor supplies
two powers of height in the denominator. Integrating over the fixed segment therefore
gives a quantity tending to zero, for both quadratic and general primitive characters.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The far-left reciprocal contour kernel's pointwise bound

The reflection and logarithmic-derivative estimates are supplied by `FarLeftReflection`.
Its quadratic and inverse-character forms feed the corresponding height-sequence bounds
below; the pointwise kernel estimate itself has no character restrictions. -/

/--
Input/assumptions: `x ≥ 1`, `σ ≤ -2`, `T ≠ 0`, and a bound `‖logDeriv (LFunction χ) (σ + T i)‖ /
T² ≤ η`.
Conclusion: `‖DirichletLFunction.dirichletReciprocalContourKernel x χ (σ + T i)‖ ≤ η` (the constant
`x` need not
appear on the right, unlike the central-strip case).
Content: same structure as
`DirichletLFunction.norm_dirichletReciprocalContourKernel_horizontal_le`, except
`‖x ^ (s - 1)‖ = x ^ (σ - 1) ≤ x ^ (-3) ≤ 1` (`σ - 1 ≤ -3` from `σ ≤ -2`, and `x ^ (-3) ≤ 1` from
`x ≥ 1`), so the numerator bound is `η * T²` rather than `η * T² * x`.
Role: the horizontal estimate pointwise kernel ingredient on the far-left strip.
-/
theorem norm_dirichletReciprocalContourKernel_farLeft_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ -2) (hT : T ≠ 0)
    (hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletReciprocalContourKernel x χ
          ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      η := by
  set s : ℂ := (σ : ℂ) + (T : ℂ) * Complex.I with hs_def
  have hsim : s.im = T := by
    simp only [hs_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsre : s.re = σ := by
    simp only [hs_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hs1im : (s - 1).im = T := by
    simp only [hs_def, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      Complex.one_im, sub_zero]
  have hxpos : (0 : ℝ) < x := by linarith
  have hxs : ‖(x : ℂ) ^ (s - 1)‖ = x ^ (σ - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, hsre, Complex.one_re]
  have hxσpos : (0 : ℝ) < x ^ (σ - 1) := Real.rpow_pos_of_pos hxpos (σ - 1)
  have hxσ_le : x ^ (σ - 1) ≤ 1 := by
    have h1 : x ^ (σ - 1) ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    rwa [Real.rpow_zero] at h1
  have htabs_pos : (0 : ℝ) < |T| := abs_pos.mpr hT
  have hsnorm_ge : |T| ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rwa [hsim] at h
  have hs1norm_ge : |T| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rwa [hs1im] at h
  have hK_eq :
    ‖dirichletReciprocalContourKernel x χ s‖ =
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (σ - 1) / (‖s‖ * ‖s - 1‖) := by
    have hlogDeriv_eq :
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ := by
      rw [logDeriv_apply]
    unfold dirichletReciprocalContourKernel
    rw [norm_div, norm_mul, norm_neg, hxs, hlogDeriv_eq, norm_mul]
  rw [hK_eq]
  have h1 :
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (σ - 1) ≤
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * 1 :=
    mul_le_mul_of_nonneg_left hxσ_le (norm_nonneg _)
  have h2 : (0 : ℝ) ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (σ - 1) := by positivity
  have h3 : T ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    calc
      T ^ 2 = |T| * |T| := by rw [← sq_abs T, sq]
      _ ≤ ‖s‖ * ‖s - 1‖ :=
        mul_le_mul hsnorm_ge hs1norm_ge htabs_pos.le (le_trans htabs_pos.le hsnorm_ge)
  have hTsq_pos : (0 : ℝ) < T ^ 2 := by positivity
  calc
    ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (σ - 1) / (‖s‖ * ‖s - 1‖) ≤
        ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x ^ (σ - 1) / T ^ 2 :=
      div_le_div_of_nonneg_left h2 hTsq_pos h3
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * 1 / T ^ 2 :=
      div_le_div_of_nonneg_right h1 hTsq_pos.le
    _ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ / T ^ 2 := by ring
    _ ≤ η := hL

/-! ### The fixed-`A` far-left horizontal integral vanishes -/

/--
Input/assumptions: `A ≥ 2`, `N ≥ 2`, `χ` primitive quadratic non-principal mod `N` with `χ⁻¹ ≠ 1`,
GRH, `x ≥ 1`.
Conclusion: there is an envelope `μ : ℕ → ℝ with μ k → 0` such that for every `k`,
`‖∫ σ in (-A - 1/2)..(-2), DirichletLFunction.dirichletReciprocalContourKernel x χ
(σ ± i (DirichletLFunction.primitiveHorizontalHeightSeq k))‖ ≤ μ k`.
Content: combines `exists_norm_logDeriv_dirichletLFunction_farLeft_le`'s `D * (T + 1)` bound with
`DirichletLFunction.norm_dirichletReciprocalContourKernel_farLeft_le`'s pointwise kernel bound
(`η_k := D * (T k +
1) / (T k)²`), then `intervalIntegral.norm_integral_le_of_norm_le_const` over the fixed-length
segment `[-A - 1/2, -2]`. `μ k := η_k * |{-2} - ({-A - 1/2})|` tends to `0` since `η_k → 0` (same
`K / T` squeeze as the central case).
Role: the horizontal estimate pointwise-integral bound, immediately squeezed to `0` below.
-/
theorem exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ μ : ℕ → ℝ,
      Filter.Tendsto μ Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletReciprocalContourKernel
                    x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq
                          hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              μ k ∧
            ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletReciprocalContourKernel
                    x χ
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
        dirichletReciprocalContourKernel x χ
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
            norm_dirichletReciprocalContourKernel_farLeft_le
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
        dirichletReciprocalContourKernel x χ
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
            norm_dirichletReciprocalContourKernel_farLeft_le
              hx hσ2 (neg_ne_zero.mpr hTk_ne) hL2')
    rwa [hμ_def, hL_def]

/--
Input/assumptions: same as
`exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le`.
Conclusion: both fixed-`A` far-left horizontal-segment integrals of the reciprocal contour kernel,
at height `± DirichletLFunction.primitiveHorizontalHeightSeq k`, tend to `0` as `k → ∞`.
Content: `squeeze_zero_norm`.
Role: the horizontal estimate checkpoint — **this completes the horizontal argument**.
-/
theorem tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral (A : ℕ) (hA : 2 ≤ A)
    {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2
                    hGRH hprimitive hne hinv hquad k *
                  Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨μ, hμ_tendsto, hμ⟩ :=
    exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le
      A hA hN2 hGRH hprimitive hne hinv hquad hx
  exact
    ⟨squeeze_zero_norm (fun k => (hμ k).1) hμ_tendsto,
      squeeze_zero_norm (fun k => (hμ k).2) hμ_tendsto⟩

/--
Input/assumptions: `A ≥ 2`, `N ≥ 2`, `χ` primitive non-principal mod `N` with `χ⁻¹ ≠ 1`, GRH (no
quadratic hypothesis), `x ≥ 1`.
Conclusion: same as
`DirichletLFunction.exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le`.
Content: use `exists_norm_logDeriv_dirichletLFunction_farLeft_le_general` and the height facts
`primitiveHorizontalHeightSeq_of_grh`, `tendsto_primitiveHorizontalHeightSeq_atTop_of_grh`,
and `primitiveHorizontalHeightSeq_ge_of_grh`;
`DirichletLFunction.norm_dirichletReciprocalContourKernel_farLeft_le` never mentioned
`χ.IsQuadratic` and is reused
verbatim.
Role: supplies the far-left integral envelope for the generic horizontal-edge limit.
-/
theorem exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le_of_grh (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ μ : ℕ → ℝ,
      Filter.Tendsto μ Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletReciprocalContourKernel
                    x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq_of_grh
                          hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              μ k ∧
            ‖∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
                  dirichletReciprocalContourKernel
                    x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq_of_grh
                          hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              μ k := by
  have hAab : -(A : ℝ) - 1 / 2 ≤ -2 := by
    have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  obtain ⟨D, hDnonneg, hD⟩ :=
    exists_norm_logDeriv_dirichletLFunction_farLeft_le_general
      A hprimitive hne hinv
  set T : ℕ → ℝ :=
    primitiveHorizontalHeightSeq_of_grh hN2 hGRH
      hprimitive hne hinv with
    hT_def
  have hT_tendsto : Filter.Tendsto T Filter.atTop Filter.atTop :=
    tendsto_primitiveHorizontalHeightSeq_atTop_of_grh
      hN2 hGRH hprimitive hne hinv
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
        primitiveHorizontalHeightSeq_ge_of_grh
          hN2 hGRH hprimitive hne hinv k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hT_def]; linarith
    have hTk_pos : (0 : ℝ) < T k := by linarith
    have hTksq_pos : (0 : ℝ) < (T k) ^ 2 := by positivity
    have hTk_ne : T k ≠ 0 := by linarith
    have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-(A : ℝ) - 1 / 2)) (b := -2) (f :=
        fun σ : ℝ =>
        dirichletReciprocalContourKernel x χ
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
            norm_dirichletReciprocalContourKernel_farLeft_le
              hx hσ2 hTk_ne hL')
    rwa [hμ_def, hL_def]
  · have hTk_ge1 : 1 ≤ T k := by
      have h :=
        primitiveHorizontalHeightSeq_ge_of_grh
          hN2 hGRH hprimitive hne hinv k
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
        dirichletReciprocalContourKernel x χ
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
            norm_dirichletReciprocalContourKernel_farLeft_le
              hx hσ2 (neg_ne_zero.mpr hTk_ne) hL2')
    rwa [hμ_def, hL_def]

/--
Input/assumptions: same as
`exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le_of_grh`.
Conclusion: both fixed-`A` far-left horizontal-segment integrals of the reciprocal contour kernel,
at height `± DirichletLFunction.primitiveHorizontalHeightSeq_of_grh k`, tend to `0` as `k → ∞` (no
quadratic
hypothesis).
Content: `squeeze_zero_norm`.
Role: supplies the far-left component of the generic horizontal-edge limit.
-/
theorem tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_of_grh (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh
                    hN2 hGRH hprimitive hne hinv k *
                  Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh
                    hN2 hGRH hprimitive hne hinv k *
                  Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨μ, hμ_tendsto, hμ⟩ :=
    exists_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral_le_of_grh
      A hA hN2 hGRH hprimitive hne hinv hx
  exact
    ⟨squeeze_zero_norm (fun k => (hμ k).1) hμ_tendsto,
      squeeze_zero_norm (fun k => (hμ k).2) hμ_tendsto⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
