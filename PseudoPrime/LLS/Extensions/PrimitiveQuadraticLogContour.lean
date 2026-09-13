/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveQuadraticLogLeftVertical
import PseudoPrime.LLS.PrimitiveLogResidueLedger
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticLogBoundary
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogExplicitFormula
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical

/-!
# Log-kernel finite-rectangle contour assembly

Logarithmic-kernel analogue of `PrimitiveQuadraticReciprocalContour.lean`'s contour assembly,
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.`
`tendsto_normalized_dirichletReciprocalBoundary_heightSeq`,
`re_characterReciprocalWeightedSum_sub_leftVertical_le`, `primitiveQuadraticReciprocalRaw`),
combining `re_sum_llsPrimitiveLogResidueAt_le` (`PrimitiveLogResidueLedger.lean`), the log-kernel
finite contour identity (`AnalyticNumberTheory/DirichletLFunction/LogContourRectangle.lean`),
the log-kernel horizontal-edge vanishing (`PrimitiveQuadraticLogHorizontalBound.lean`),
and the log-kernel left-vertical edge (`PrimitiveQuadraticLogLeftVertical.lean`).
Unlike the reciprocal case, no square-completion algebra is needed:
`re_sum_llsPrimitiveLogResidueAt_le`'s bound is already in the final target shape, so the
`k → ∞`/`A → ∞` limit transfer directly yields the target theorem,
`primitiveQuadraticLogWeightedUpper`.
-/

namespace PseudoPrime.LLS.Extensions

/-! ### Fixed-`A`, `k → ∞` contour boundary limit, log kernel -/

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`,
`A ≥ 2`.
Conclusion: `Re(S(x,χ)) - (2π)⁻¹ Re(∫t,K_log(λ_A+it)) ≤ (2√x+2+log x)|Re B(χ)| +
(1/2)(log N - log π) log x - 11/4`.
Content: for each `k`, `.re` of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.`
`dirichletLogFiniteContourIdentity_heightSeq_normalized`
combined with `re_sum_llsPrimitiveLogResidueAt_le` (fed by
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.`
`primitiveReciprocalMellinPoints_mem_singularities_heightSeq`) bounds the normalized boundary's
real part by the constant, uniformly in `k`; transferring through
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.`
`tendsto_normalized_dirichletLogBoundary_heightSeq`'s
`k → ∞` limit via `le_of_tendsto` gives the
fixed-`A` bound.
Role: the fixed-`A` estimate used in the `A → ∞` assembly.
-/
theorem re_characterLogWeightedSum_sub_leftVertical_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              AnalyticNumberTheory.DirichletLFunction.dirichletLogContourKernel x χ
                (((AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I)).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have htend :=
    AnalyticNumberTheory.DirichletLFunction.tendsto_normalized_dirichletLogBoundary_heightSeq
      hN2 hGRH hprimitive hne hinv hquad hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (AnalyticNumberTheory.DirichletLFunction.dirichletLogContourKernel x χ)
              (AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLowerCorner
                hN2 hGRH hprimitive hne hinv hquad A k)
              (AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalUpperCorner
                hN2 hGRH hprimitive hne hinv hquad k)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards with k
    have hid :=
      AnalyticNumberTheory.DirichletLFunction.dirichletLogFiniteContourIdentity_heightSeq_normalized
        hN2 hGRH hprimitive hne hinv hquad (by linarith : (0 : ℝ) < x) A k hA
    open AnalyticNumberTheory.DirichletLFunction in
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq
        hN2 hGRH hprimitive hne hinv hquad A k hA
    have hbound :=
      re_sum_llsPrimitiveLogResidueAt_le hN2 hGRH hprimitive hne hinv hquad hx (z :=
        AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLowerCorner hN2 hGRH
          hprimitive hne hinv hquad A k)
        (w :=
        AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalUpperCorner hN2 hGRH
          hprimitive hne hinv hquad k)
        h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              AnalyticNumberTheory.DirichletLFunction.dirichletLogContourKernel x χ
                (((AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            AnalyticNumberTheory.DirichletLFunction.dirichletLogContourKernel x χ
              (((AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLeftRe A :
                    ℝ) :
                  ℂ) +
                (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`.
Conclusion:
`Re(S(x,χ)) ≤ (2√x+2+log x)|Re B(χ)| + (1/2)(log N - log π) log x - 11/4`.
Content: `re_characterLogWeightedSum_sub_leftVertical_le` holds for every `A ≥ 2`; the subtracted
term `(2π)⁻¹ Re(∫t,K_log(λ_A+it))` tends to `0` as `A → ∞` by
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.`
`quadraticTendsto_dirichletLogContourKernel_leftVertical_integral_atTop`
(continuity of `Complex.re`);
transferring through this limit via `le_of_tendsto` removes the left-vertical term entirely.
Role: the raw quadratic log-weighted-sum upper bound used by `PrimitiveQuadraticLemma22.lean`.
-/
theorem primitiveQuadraticLogWeightedUpper {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) < x := by linarith
  open AnalyticNumberTheory.DirichletLFunction in
  have htend := quadraticTendsto_dirichletLogContourKernel_leftVertical_integral_atTop
      hprimitive hne hquad hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  simp only [Complex.zero_re] at htendRe
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                AnalyticNumberTheory.DirichletLFunction.dirichletLogContourKernel x χ
                  (((AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re)
      Filter.atTop
      (nhds
        ((AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                AnalyticNumberTheory.DirichletLFunction.dirichletLogContourKernel x χ
                  (((AnalyticNumberTheory.DirichletLFunction.primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact re_characterLogWeightedSum_sub_leftVertical_le hN2 hGRH hprimitive hne hinv hquad hx A hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.LLS.Extensions
