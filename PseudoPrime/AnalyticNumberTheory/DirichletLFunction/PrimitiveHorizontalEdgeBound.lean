/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveOrdinaryLogDerivBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SmoothedContour

/-!
# Horizontal pointwise bound for the reciprocal contour kernel

Bounds `‖DirichletLFunction.dirichletReciprocalContourKernel x χ s‖` on a horizontal line `s = σ +
T i` (`|σ| ≤ 2`,
`x ≥ 1`) by `x * η`, given a bound `‖logDeriv (LFunction χ) s‖ / T² ≤ η` on the ordinary
log-derivative (as supplied by
`DirichletLFunction.exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small`). This is purely
mechanical: no
primitivity, quadratic, or GRH hypotheses on `χ` are needed at this pointwise level.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `x ≥ 1`, `|σ| ≤ 2`, `T ≠ 0`, and a bound
`‖logDeriv (LFunction χ) (σ + T i)‖ / T² ≤ η` on the ordinary log-derivative.
Conclusion: `‖DirichletLFunction.dirichletReciprocalContourKernel x χ (σ + T i)‖ ≤ x * η`.
Content: `‖x ^ (s - 1)‖ = x ^ (σ - 1) ≤ x ^ 1 = x` (`Complex.norm_cpow_eq_rpow_re_of_pos` +
`Real.rpow_le_rpow_of_exponent_le`, since `σ - 1 ≤ 1` from `|σ| ≤ 2`); `T² ≤ ‖s‖ * ‖s - 1‖`
(`Complex.abs_im_le_norm` applied to `s` and `s - 1`, both of which have imaginary part `T`); the
kernel unfolds to `‖logDeriv (LFunction χ) s‖ * ‖x ^ (s - 1)‖ / (‖s‖ * ‖s - 1‖)`, so combining the
two bounds and the numerator hypothesis `hL` gives `≤ x * η`.
Role: the horizontal estimate pointwise ingredient, feeding the central `[-2, 2]` and fixed-`A`
far-left
horizontal integral bounds.
-/
theorem norm_dirichletReciprocalContourKernel_horizontal_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {x σ T η : ℝ} (hx : 1 ≤ x) (hσ : |σ| ≤ 2) (hT : T ≠ 0)
    (hL : ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (T : ℂ) * Complex.I)‖ / T ^ 2 ≤ η) :
    ‖dirichletReciprocalContourKernel x χ
          ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      x * η := by
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
  have hxσ_le : x ^ (σ - 1) ≤ x := by
    have h1 : x ^ (σ - 1) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx
        (by
          have := abs_le.mp hσ; linarith)
    rwa [Real.rpow_one] at h1
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
      ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x :=
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
    _ ≤ ‖logDeriv (DirichletCharacter.LFunction χ) s‖ * x / T ^ 2 :=
      div_le_div_of_nonneg_right h1 hTsq_pos.le
    _ = ‖logDeriv (DirichletCharacter.LFunction χ) s‖ / T ^ 2 * x := by ring
    _ ≤ η * x := by apply mul_le_mul_of_nonneg_right hL hxpos.le
    _ = x * η := by ring

/--
Input/assumptions: `N ≥ 2`, `χ` primitive quadratic non-principal mod `N` with `χ⁻¹ ≠ 1`, GRH,
`x ≥ 1`.
Conclusion: there is an envelope `η : ℕ → ℝ with η k → 0` such that for every `k` and every `σ` with
`|σ| ≤ 2`, `‖DirichletLFunction.dirichletReciprocalContourKernel x χ (σ ± i
(DirichletLFunction.primitiveHorizontalHeightSeq k))‖ ≤
x * η k`.
Content: combines `DirichletLFunction.exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small`
with
`DirichletLFunction.norm_dirichletReciprocalContourKernel_horizontal_le`, applied at
`T := DirichletLFunction.primitiveHorizontalHeightSeq k` and `T :=
-(DirichletLFunction.primitiveHorizontalHeightSeq k)` (both nonzero
since `DirichletLFunction.primitiveHorizontalHeightSeq k ≥ k + 1 ≥ 1 > 0`); the minus branch uses
`(σ : ℂ) - T k * I = (σ : ℂ) + (-(T k)) * I`.
Role: supplies the pointwise envelope for the central horizontal integral bound.
-/
theorem exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 →
              ‖dirichletReciprocalContourKernel
                      x χ
                      ((σ : ℂ) +
                        primitiveHorizontalHeightSeq
                            hN2 hGRH hprimitive hne hinv hquad k *
                          Complex.I)‖ ≤
                  x * η k ∧
                ‖dirichletReciprocalContourKernel
                      x χ
                      ((σ : ℂ) -
                        primitiveHorizontalHeightSeq
                            hN2 hGRH hprimitive hne hinv hquad k *
                          Complex.I)‖ ≤
                  x * η k := by
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
    ⟨norm_dirichletReciprocalContourKernel_horizontal_le
        hx hσ hTk_ne (hη k σ hσ).1,
      ?_⟩
  have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hform]
  have hL2 := (hη k σ hσ).2
  rw [hform, ← neg_sq] at hL2
  exact
    norm_dirichletReciprocalContourKernel_horizontal_le
      hx hσ (neg_ne_zero.mpr hTk_ne) hL2

/--
Input/assumptions: `N ≥ 2`, `χ` primitive non-principal mod `N` with `χ⁻¹ ≠ 1`, GRH (no quadratic
hypothesis), `x ≥ 1`.
Conclusion: same as `DirichletLFunction.exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound`.
Content: identical, built on the `hquad`-free
`DirichletLFunction.exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small_of_grh` and
`DirichletLFunction.primitiveHorizontalHeightSeq_ge_of_grh` instead;
`norm_dirichletReciprocalContourKernel_horizontal_le` never mentioned `χ.IsQuadratic` and is reused
verbatim.
Role: supplies the pointwise envelope for the generic central horizontal integral bound.
-/
theorem exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ∀ σ : ℝ,
            |σ| ≤ 2 →
              ‖dirichletReciprocalContourKernel
                      x χ
                      ((σ : ℂ) +
                        primitiveHorizontalHeightSeq_of_grh
                            hN2 hGRH hprimitive hne hinv k *
                          Complex.I)‖ ≤
                  x * η k ∧
                ‖dirichletReciprocalContourKernel
                      x χ
                      ((σ : ℂ) -
                        primitiveHorizontalHeightSeq_of_grh
                            hN2 hGRH hprimitive hne hinv k *
                          Complex.I)‖ ≤
                  x * η k := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_envelope_primitiveHorizontalHeightSeq_LLogDeriv_small_of_grh
      hN2 hGRH hprimitive hne hinv
  refine ⟨η, hη_tendsto, fun k σ hσ => ?_⟩
  set T : ℕ → ℝ :=
    primitiveHorizontalHeightSeq_of_grh hN2 hGRH
      hprimitive hne hinv with
    hT_def
  have hTk_ge1 : 1 ≤ T k := by
    have h :=
      primitiveHorizontalHeightSeq_ge_of_grh hN2
        hGRH hprimitive hne hinv k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [hT_def]; linarith
  have hTk_ne : T k ≠ 0 := by linarith
  refine
    ⟨norm_dirichletReciprocalContourKernel_horizontal_le
        hx hσ hTk_ne (hη k σ hσ).1,
      ?_⟩
  have hform : (σ : ℂ) - (T k : ℂ) * Complex.I = (σ : ℂ) + ((-(T k) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hform]
  have hL2 := (hη k σ hσ).2
  rw [hform, ← neg_sq] at hL2
  exact
    norm_dirichletReciprocalContourKernel_horizontal_le
      hx hσ (neg_ne_zero.mpr hTk_ne) hL2

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
