/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFarLeftHorizontalBound
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveContourRectangle
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLeftVerticalBound
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveExplicitFormula

/-!
# Generic horizontal-edge continuity

The height-line continuity certificate for the reciprocal kernel is independent of quadratic
self-duality.  It is separated from the pointwise bound so the generic central and far-left
consumers can share the same interval-integrability interface.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under GRH, for a primitive nontrivial character of level `N ≥ 2` with nontrivial
inverse and `x > 0`, the reciprocal kernel is continuous along both selected horizontal
lines. Positive good heights avoid `0`, `1`, and all L-function zeros, so differentiability
of the kernel gives continuity. This supplies integrability of the horizontal edges. -/
theorem continuous_dirichletReciprocalContourKernel_horizontalHeightSeq {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Continuous
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) ∧
      Continuous
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) := by
  have hT := primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv k
  have hTpos : (0 : ℝ) < primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith only [hT, hk]
  have hpt :
    ∀ s : ℂ,
      s.im = primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k ∨
          s.im = -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k) →
        ContinuousAt (dirichletReciprocalContourKernel x χ) s := by
    intro s hs
    have hsne : s.im ≠ 0 := by
      rcases hs with hs | hs
      · rw [hs]
        exact hTpos.ne'
      · rw [hs]
        exact (neg_lt_zero.mpr hTpos).ne
    have hs0 : s ≠ 0 := fun h =>
      hsne
        (by
          rw [h]
          simp only [Complex.zero_im])
    have hs1 : s ≠ 1 := fun h =>
      hsne
        (by
          rw [h]
          simp only [Complex.one_im])
    have hL :=
      dirichletLFunction_ne_zero_of_im_eq_primitiveHeightSeq hN2 hGRH hprimitive hne hinv k hs
    exact (differentiableAt_dirichletReciprocalContourKernel hx hne hs0 hs1 hL).continuousAt
  constructor
  · have hg :
      Continuous
        (fun σ : ℝ =>
          (σ : ℂ) +
            (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn (dirichletReciprocalContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) +
              (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I)) := by
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
            (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I) := by
      fun_prop
    have hOn :
      ContinuousOn (dirichletReciprocalContourKernel x χ)
        (Set.range
          (fun σ : ℝ =>
            (σ : ℂ) -
              (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k : ℂ) * Complex.I)) := by
      rintro s ⟨σ, rfl⟩
      exact
        (hpt _
            (Or.inr
              (by
                simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
                  Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
                  zero_sub]))).continuousWithinAt
    exact hOn.comp_continuous hg (fun σ => Set.mem_range_self σ)

/-- For the same primitive-character GRH hypotheses and `x > 0`, both selected horizontal
reciprocal kernels are integrable on any real interval `a..b`. Apply continuity on each
line; this permits adjacent-interval decompositions without restrictions on the endpoints. -/
theorem intervalIntegrable_dirichletReciprocalContourKernel_horizontalHeightSeq {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ)
    (a b : ℝ) :
    IntervalIntegrable
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        MeasureTheory.volume a b := by
  have h :=
    continuous_dirichletReciprocalContourKernel_horizontalHeightSeq hN2 hGRH hprimitive hne hinv hx
      k
  exact ⟨h.1.intervalIntegrable a b, h.2.intervalIntegrable a b⟩

/-- For a primitive nontrivial character with nontrivial inverse under GRH and `x > 0`,
specialize horizontal-line integrability to `[-2,2]` at both selected heights. This gives
the central-segment input for splitting the reciprocal horizontal edges. -/
theorem intervalIntegrable_dirichletReciprocalContourKernel_central {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntervalIntegrable
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        MeasureTheory.volume (-2) 2 ∧
      IntervalIntegrable
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        MeasureTheory.volume (-2) 2 := by
  exact
    intervalIntegrable_dirichletReciprocalContourKernel_horizontalHeightSeq hN2 hGRH hprimitive hne
      hinv hx k (-2) 2

/-- Under the primitive-character GRH hypotheses and `x > 0`, the reciprocal kernels
at both selected heights are integrable on `(-A-1/2)..(-2)` for any natural `A`.
Specialize arbitrary-interval integrability; no `A ≥ 2` condition is required for this
oriented-interval statement used in the edge decomposition. -/
theorem intervalIntegrable_dirichletReciprocalContourKernel_farLeft (A : ℕ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntervalIntegrable
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        MeasureTheory.volume (-(A : ℝ) - 1 / 2) (-2) ∧
      IntervalIntegrable
        (fun σ : ℝ =>
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        MeasureTheory.volume (-(A : ℝ) - 1 / 2) (-2) := by
  exact
    intervalIntegrable_dirichletReciprocalContourKernel_horizontalHeightSeq hN2 hGRH hprimitive hne
      hinv hx k (-(A : ℝ) - 1 / 2) (-2)

/-- Under the primitive-character GRH hypotheses and `x > 0`, split the upper reciprocal
horizontal integral from `-A-1/2` to `2` at `-2`. Integrability of the two segments gives
adjacent-interval additivity for any natural `A`; this combines far-left and central limits. -/
theorem intervalIntegral_add_adjacent_dirichletReciprocalKernel (A : ℕ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
        ∫ σ in (-2 : ℝ)..(2 : ℝ),
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) =
      ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
        dirichletReciprocalContourKernel x χ
          ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) := by
  apply intervalIntegral.integral_add_adjacent_intervals
  · exact
      (intervalIntegrable_dirichletReciprocalContourKernel_farLeft A hN2 hGRH hprimitive hne hinv hx
          k).1
  · exact
      (intervalIntegrable_dirichletReciprocalContourKernel_central hN2 hGRH hprimitive hne hinv hx
          k).1

/-- Under the primitive-character GRH hypotheses and `x > 0`, split the lower reciprocal
horizontal integral from `-A-1/2` to `2` at `-2`. Apply adjacent-interval additivity to the
integrable lower segments; this is the lower-edge counterpart of the upper decomposition. -/
theorem intervalIntegral_add_adjacent_dirichletReciprocalKernel_lower (A : ℕ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
        ∫ σ in (-2 : ℝ)..(2 : ℝ),
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) =
      ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
        dirichletReciprocalContourKernel x χ
          ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) := by
  apply intervalIntegral.integral_add_adjacent_intervals
  · exact
      (intervalIntegrable_dirichletReciprocalContourKernel_farLeft A hN2 hGRH hprimitive hne hinv hx
          k).2
  · exact
      (intervalIntegrable_dirichletReciprocalContourKernel_central hN2 hGRH hprimitive hne hinv hx
          k).2

/-- Under the primitive-character GRH hypotheses and `x > 0`, package both decompositions
of the full reciprocal horizontal edges at `-2`. Pair the upper and lower adjacent-interval
identities so the far-left and central convergence estimates use the same height sequence. -/
theorem intervalIntegral_add_adjacent_dirichletReciprocalKernel_pair (A : ℕ) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
          ∫ σ in (-2 : ℝ)..2,
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..2,
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) ∧
      (∫ σ in (-(A : ℝ) - 1 / 2)..(-2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
          ∫ σ in (-2 : ℝ)..2,
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) =
        ∫ σ in (-(A : ℝ) - 1 / 2)..2,
          dirichletReciprocalContourKernel x χ
            ((σ : ℂ) -
              primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) := by
  exact
    ⟨intervalIntegral_add_adjacent_dirichletReciprocalKernel A hN2 hGRH hprimitive hne hinv hx k,
      intervalIntegral_add_adjacent_dirichletReciprocalKernel_lower A hN2 hGRH hprimitive hne hinv
        hx k⟩

/-- Under GRH, for a primitive nontrivial character with nontrivial inverse, `N ≥ 2`,
`A ≥ 2`, and `x ≥ 1`, both reciprocal horizontal integrals from `-A-1/2` to `2` tend to
zero along the selected heights. Add the far-left and central limits using the paired
split identities; this removes the horizontal edges from the boundary limit. -/
theorem tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_horizontal_integral (A : ℕ)
    (hA : 2 ≤ A) {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
            dirichletReciprocalContourKernel x χ
              ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I))
        Filter.atTop (nhds 0) := by
  have hfar :=
    tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_farLeft_integral A hA hN2 hGRH hprimitive
      hne hinv hx
  have hcentral :=
    tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_central_integral hN2 hGRH hprimitive hne
      hinv hx
  have hsplit := fun k : ℕ =>
    intervalIntegral_add_adjacent_dirichletReciprocalKernel_pair A hN2 hGRH hprimitive hne hinv
      (by linarith only [hx]) k
  constructor
  · have h := hfar.1.add hcentral.1
    simpa only [add_zero] using h.congr (fun k => (hsplit k).1)
  · have h := hfar.2.add hcentral.2
    simpa only [add_zero] using h.congr (fun k => (hsplit k).2)

/-- Under the same primitive-character GRH hypotheses, `A ≥ 2`, and `x ≥ 1`, the
normalized lower-minus-upper reciprocal horizontal contribution tends to zero.
Subtract the two full-edge limits and multiply by `-i/(2π)`; this matches the horizontal
term in the normalized rectangle-boundary decomposition. -/
theorem tendsto_normalized_primitiveHorizontalReciprocalEdge (A : ℕ) (hA : 2 ≤ A) {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
              dirichletReciprocalContourKernel x χ
                ((σ : ℂ) -
                  primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) -
            ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
              dirichletReciprocalContourKernel x χ
                ((σ : ℂ) +
                  primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)))
      Filter.atTop (nhds 0) := by
  have hhoriz :=
    tendsto_primitiveHorizontalHeightSeq_reciprocalKernel_horizontal_integral A hA hN2 hGRH
      hprimitive hne hinv hx
  have hdiff := hhoriz.2.sub hhoriz.1
  simpa only [sub_zero, mul_zero] using
    (Filter.Tendsto.const_mul (-Complex.I / (2 * (Real.pi : ℂ))) hdiff)

/--
Input/assumptions: `N ≥ 2`, a primitive nontrivial character and its nontrivial inverse, GRH,
`x ≥ 1`, and `A ≥ 2`.
Conclusion: the normalized reciprocal contour boundary of the generic height-sequence rectangle
converges to the right-edge weighted sum minus the normalized whole left-edge integral.
Content: unfolds the generic corners; the normalized horizontal contribution tends to zero, while
the right and left vertical truncations converge along the same generic height sequence.
Role: supplies the normalized boundary limit for the finite reciprocal residue ledger.
-/
theorem tendsto_normalized_dirichletReciprocalBoundary_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (A : ℕ)
    (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletReciprocalContourKernel x χ)
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k))
      Filter.atTop
      (nhds
        (Arithmetic.characterReciprocalWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  have hcoeffI : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]
        ring]
    push_cast
    ring
  have hcoeff : (((2 * Real.pi : ℝ) : ℂ)⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by norm_cast
  have heq :
    ∀ k : ℕ,
      (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletReciprocalContourKernel x χ)
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) =
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletReciprocalContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
                dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    intro k
    have hzre :
      (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k).re =
        primitiveReciprocalLeftRe A := by
      rw [primitiveHeightSeqLowerCorner]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
    have hzim :
      (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k).im =
        -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k) := by
      rw [primitiveHeightSeqLowerCorner]
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]
    have hwre : (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k).re = 2 := by
      rw [primitiveHeightSeqUpperCorner]
      simp only [Complex.ofReal_ofNat, Complex.add_re, Complex.re_ofNat, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, add_zero]
    have hwim :
      (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k).im =
        primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k := by
      rw [primitiveHeightSeqUpperCorner]
      simp only [Complex.ofReal_ofNat, Complex.add_im, Complex.im_ofNat, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add]
    unfold RectangleGeometry.rectangleBoundaryIntegral
    rw [hzre, hzim, hwre, hwim, primitiveReciprocalLeftRe]
    simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul]
    linear_combination
      (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
            dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI -
        (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
            dirichletReciprocalContourKernel x χ
              (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI
  apply Filter.Tendsto.congr (fun k => (heq k).symm)
  have hhoriz :=
    tendsto_normalized_primitiveHorizontalReciprocalEdge A hA hN2 hGRH hprimitive hne hinv hx
  have hright :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ t in
          (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
              k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
          dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds (∫ t : ℝ, dirichletReciprocalContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I))) :=
    (tendsto_intervalIntegral_dirichletReciprocalContourKernel hxpos χ hne
          (show (1 : ℝ) < 2 from by norm_num only)).comp
      (tendsto_primitiveHorizontalHeightSeq_atTop hN2 hGRH hprimitive hne hinv)
  have hleft :=
    tendsto_primitiveHorizontalHeightSeq_leftVertical_intervalIntegral hN2 hGRH hprimitive hne hinv
      hxpos hA
  have hleft' :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ t in
          (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
              k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
          dirichletReciprocalContourKernel x χ
            (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds
        (∫ t : ℝ,
          dirichletReciprocalContourKernel x χ
            (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
    simpa only [primitiveReciprocalLeftRe] using hleft
  have hweighted :=
    characterReciprocalWeightedSum_eq_integral χ hxpos (show (1 : ℝ) < 2 from by norm_num only)
  have htarget :=
    (hhoriz.add (Filter.Tendsto.const_mul ((2 * Real.pi : ℝ)⁻¹ : ℂ) hright)).sub
      (Filter.Tendsto.const_mul ((2 * Real.pi : ℝ)⁻¹ : ℂ) hleft')
  rw [hweighted, Complex.real_smul]
  rw [← hcoeff]
  convert htarget using 2
  all_goals push_cast
  all_goals ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
