/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalEdgeBound

/-!
# Central horizontal reciprocal-kernel integrals vanish

Integrate the pointwise reciprocal-kernel envelope over the length-four segment
`[-2, 2]` at the selected positive and negative heights. The interval-integral norm bound
and the envelope limit imply convergence to zero, both for quadratic characters and for
the general primitive-character GRH height sequence.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `N ≥ 2`, `χ` primitive quadratic non-principal mod `N` with `χ⁻¹ ≠ 1`, GRH,
`x ≥ 1`.
Conclusion: there is an envelope `η : ℕ → ℝ with η k → 0` such that for every `k`,
`‖∫ σ in -2..2, DirichletLFunction.dirichletReciprocalContourKernel x χ (σ ± i
(DirichletLFunction.primitiveHorizontalHeightSeq k))‖ ≤
4 * x * η k`.
Content: `intervalIntegral.norm_integral_le_of_norm_le_const` with the constant
`x * η k` from `DirichletLFunction.exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound`,
over the
fixed-length-`4` segment `[-2, 2]`.
Role: the horizontal estimate pointwise-integral bound, immediately squeezed to `0` below.
-/
theorem exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-2 : ℝ)..2,
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              4 * (x * η k) ∧
            ‖∫ σ in (-2 : ℝ)..2,
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)‖ ≤
              4 * (x * η k) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound hN2 hGRH hprimitive hne hinv hquad hx
  refine ⟨η, hη_tendsto, fun k => ⟨?_, ?_⟩⟩
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletReciprocalContourKernel x χ
          ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I))
        (C := x * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).1)
    rw [show |(2 : ℝ) - (-2)| = 4 from by norm_num only] at hbound
    linarith
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletReciprocalContourKernel x χ
          ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I))
        (C := x * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).2)
    rw [show |(2 : ℝ) - (-2)| = 4 from by norm_num only] at hbound
    linarith

/--
Input/assumptions: same as
`DirichletLFunction.exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le`.
Conclusion: both central horizontal-segment integrals of the reciprocal contour kernel, at height
`± DirichletLFunction.primitiveHorizontalHeightSeq k`, tend to `0` as `k → ∞`.
Content: `4 * x * η k → 0` since `η k → 0`, then `squeeze_zero_norm`.
Role: the horizontal estimate checkpoint (central horizontal integral vanishes).
-/
theorem tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k * Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le hN2 hGRH hprimitive hne
      hinv hquad hx
  have htend : Filter.Tendsto (fun k : ℕ => 4 * (x * η k)) Filter.atTop (nhds 0) := by
    have := hη_tendsto.const_mul (4 * x)
    simpa only [mul_assoc, mul_zero] using this
  exact ⟨squeeze_zero_norm (fun k => (hη k).1) htend, squeeze_zero_norm (fun k => (hη k).2) htend⟩

/--
Input/assumptions: `N ≥ 2`, `χ` primitive non-principal mod `N` with `χ⁻¹ ≠ 1`, GRH (no quadratic
hypothesis), `x ≥ 1`.
Conclusion: same as
`DirichletLFunction.exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le`.
Content: identical, built on the `hquad`-free
`DirichletLFunction.exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound_of_grh` instead;
`intervalIntegral.norm_integral_le_of_norm_le_const` never mentioned `χ.IsQuadratic` and is reused
verbatim.
Role: supplies the central integral envelope for the generic horizontal-edge limit.
-/
theorem exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le_of_grh {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ η : ℕ → ℝ,
      Filter.Tendsto η Filter.atTop (nhds 0) ∧
        ∀ k : ℕ,
          ‖∫ σ in (-2 : ℝ)..2,
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              4 * (x * η k) ∧
            ‖∫ σ in (-2 : ℝ)..2,
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k *
                        Complex.I)‖ ≤
              4 * (x * η k) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_reciprocalKernel_bound_of_grh hN2 hGRH hprimitive hne hinv
      hx
  refine ⟨η, hη_tendsto, fun k => ⟨?_, ?_⟩⟩
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletReciprocalContourKernel x χ
          ((σ : ℂ) +
            primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        (C := x * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).1)
    rw [show |(2 : ℝ) - (-2)| = 4 from by norm_num only] at hbound
    linarith
  · have hbound :=
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (-2 : ℝ)) (b := 2) (f := fun σ : ℝ =>
        dirichletReciprocalContourKernel x χ
          ((σ : ℂ) -
            primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        (C := x * η k)
        (by
          rw [Set.uIoc_of_le (by norm_num only : (-2 : ℝ) ≤ 2)]
          rintro σ ⟨hσ1, hσ2⟩
          exact (hη k σ (abs_le.mpr ⟨hσ1.le, hσ2⟩)).2)
    rw [show |(2 : ℝ) - (-2)| = 4 from by norm_num only] at hbound
    linarith

/--
Input/assumptions: same as
`exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le_of_grh`.
Conclusion: both central horizontal-segment integrals of the reciprocal contour kernel, at height
`± DirichletLFunction.primitiveHorizontalHeightSeq_of_grh k`, tend to `0` as `k → ∞` (no quadratic
hypothesis).
Content: `4 * x * η k → 0` since `η k → 0`, then `squeeze_zero_norm`.
Role: supplies the central component of the generic horizontal-edge limit.
-/
theorem tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_of_grh {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) +
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-2 : ℝ)..2,
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) -
                primitiveHorizontalHeightSeq_of_grh hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) := by
  obtain ⟨η, hη_tendsto, hη⟩ :=
    exists_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral_le_of_grh hN2 hGRH
      hprimitive hne hinv hx
  have htend : Filter.Tendsto (fun k : ℕ => 4 * (x * η k)) Filter.atTop (nhds 0) := by
    have := hη_tendsto.const_mul (4 * x)
    simpa only [mul_assoc, mul_zero] using this
  exact ⟨squeeze_zero_norm (fun k => (hη k).1) htend, squeeze_zero_norm (fun k => (hη k).2) htend⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
