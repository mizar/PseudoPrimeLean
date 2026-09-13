/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds
import PseudoPrime.LLS.Extensions.QNeOneNumerics
import PseudoPrime.Analysis.LogarithmicMainTerms
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveContourRectangle
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticReciprocalBoundary
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenResidueClosedForm
import PseudoPrime.LLS.PrimitiveReciprocalMainErrorBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveExplicitFormula
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericHorizontalEdge

/-!
# Uniform upper bound for the finite reciprocal residue sum

Assembles the whole primitive singularity ledger's residue sum real-part bound, uniform in the
choice of rectangle (in particular `A`, `k`-independent): splits off `r₀ + r₁`
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletSplitReciprocalSingularitySum`),
bounds it by parity dispatch (the odd/even closed
forms plus the bounds in `LLS/PrimitiveReciprocalMainErrorBounds.lean`), and combines with the
erased-ledger zero-mass bound from `PrimitiveMultiplicityBridge.lean`.
-/

namespace PseudoPrime.LLS.Extensions

/-!
The even branch has a stronger remainder than the parity-uniform `-1/4` estimate.  This theorem
keeps that improvement separate so the existing generic raw API remains unchanged.
-/

theorem re_add_llsPrimitiveReciprocalResidues_zero_one_even_lt {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ}
    (hx : 64 ≤ x) :
    (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 0 +
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x
            1).re <
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
        (1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| -
        4 / 5 := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hraw :=
    AnalyticNumberTheory.DirichletLFunction.re_add_dirichletReciprocalResidues_zero_one_of_even_raw
      hN2 hGRH hprimitive hne hinv heven hxpos
  have herr := llsPrimitiveReciprocalEvenMainError_lt_neg_four_fifths hx
  unfold Analysis.primitiveReciprocalEvenMainError at herr
  rw [hraw]
  nlinarith [herr]

/-! ### Fixed-`A`, `k → ∞` contour boundary limit -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`,
`A ≥ 2`.
Conclusion:
`Re(R(x,χ)) - (2π)⁻¹ Re(∫t,K(λ_A+it)) ≤ (1/2)(1-1/x)(log N-log π) - 1/4 - (1-1/√x)²|Re B(χ)|`.
Content: for each `k`, `.re` of
`DirichletLFunction.dirichletReciprocalFiniteContourIdentity_heightSeq_normalized`
combined with `re_sum_llsPrimitiveReciprocalResidueAt_le` (fed by
`DirichletLFunction.primitiveReciprocalMellinPoints_mem_singularities_heightSeq`)
bounds the normalized boundary's
real part by the constant `C(x,N,χ)`, uniformly in `k`; transferring through
`DirichletLFunction.tendsto_normalized_dirichletReciprocalBoundary_heightSeq`'s
`k → ∞` limit via `le_of_tendsto`
(continuity of `Complex.re`) gives the fixed-`A` bound.
Role: ready for the `A → ∞` assembly using the left-vertical
whole-line integral vanishing.
-/
theorem re_characterReciprocalWeightedSum_sub_leftVertical_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (characterReciprocalWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I)).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
        (1 - 1 / Real.sqrt x) ^ 2 *
          |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have htend :=
    tendsto_normalized_dirichletReciprocalBoundary_heightSeq
      hN2 hGRH hprimitive hne hinv hquad hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletReciprocalContourKernel
                x χ)
              (primitiveReciprocalLowerCorner
                hN2 hGRH hprimitive hne hinv hquad A k)
              (primitiveReciprocalUpperCorner
                hN2 hGRH hprimitive hne hinv hquad k)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
          (1 - 1 / Real.sqrt x) ^ 2 *
            |primitiveBRe χ| := by
    filter_upwards with k
    have hid :=
      dirichletReciprocalFiniteContourIdentity_heightSeq_normalized
        hN2 hGRH hprimitive hne hinv hquad (by linarith : (0 : ℝ) < x) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq
        hN2 hGRH hprimitive hne hinv hquad A k hA
    have hbound :=
      re_sum_llsPrimitiveReciprocalResidueAt_le hN2 hGRH hprimitive hne hinv hx (z :=
        primitiveReciprocalLowerCorner hN2 hGRH
          hprimitive hne hinv hquad A k)
        (w :=
        primitiveReciprocalUpperCorner hN2 hGRH
          hprimitive hne hinv hquad k)
        h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletReciprocalContourKernel x χ
              (((primitiveReciprocalLeftRe A :
                    ℝ) :
                  ℂ) +
                (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/-!
The fixed-left-edge quadratic contour estimate with the strong even remainder.  It mirrors the
existing `-1/4` interface but consumes the even residue theorem above.
-/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem re_characterReciprocalWeightedSum_sub_leftVertical_lt_of_even {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (heven : χ.Even) {x : ℝ} (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (characterReciprocalWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I)).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
        (1 - 1 / Real.sqrt x) ^ 2 *
          |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have htend :=
    tendsto_normalized_dirichletReciprocalBoundary_heightSeq
      hN2 hGRH hprimitive hne hinv hquad hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletReciprocalContourKernel
                x χ)
              (primitiveReciprocalLowerCorner
                hN2 hGRH hprimitive hne hinv hquad A k)
              (primitiveReciprocalUpperCorner
                hN2 hGRH hprimitive hne hinv hquad k)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
          (1 - 1 / Real.sqrt x) ^ 2 *
            |primitiveBRe χ| := by
    filter_upwards with k
    have hid :=
      dirichletReciprocalFiniteContourIdentity_heightSeq_normalized
        hN2 hGRH hprimitive hne hinv hquad (by linarith : (0 : ℝ) < x) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq
        hN2 hGRH hprimitive hne hinv hquad A k hA
    have hbound :=
      re_add_llsPrimitiveReciprocalResidues_zero_one_even_lt hN2 hGRH hprimitive hne hinv heven hx
    rw [hid]
    have hsum :=
      re_sum_erased_primitiveReciprocalResidues_le
        hN2 hGRH hprimitive hne hinv (by linarith : (0 : ℝ) < x) (z :=
        primitiveReciprocalLowerCorner hN2 hGRH
          hprimitive hne hinv hquad A k)
        (w :=
        primitiveReciprocalUpperCorner hN2 hGRH
          hprimitive hne hinv hquad k)
    rw [dirichletSplitReciprocalSingularitySum x
        hne h1 h0]
    rw [Complex.add_re, Complex.add_re]
    have hsqrtx_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
    have hinv_sqrt_sq : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [div_pow, one_pow, hsqrt_sq]
    have hbcoeff :
      -(1 + 1 / x) * |primitiveBRe χ| +
          2 * |primitiveBRe χ| / Real.sqrt x =
        -(1 - 1 / Real.sqrt x) ^ 2 *
          |primitiveBRe χ| := by
      have hsqrtx_ne : Real.sqrt x ≠ 0 := hsqrtx_pos.ne'
      have hexpand : (1 - 1 / Real.sqrt x) ^ 2 = 1 - 2 / Real.sqrt x + 1 / x := by
        rw [sub_sq, one_pow, hinv_sqrt_sq]
        ring
      rw [hexpand]
      ring
    calc
      (dirichletReciprocalResidueAt hne x
                1).re +
            (dirichletReciprocalResidueAt hne x
                0).re +
            (∑
                ρ ∈
                  ((dirichletLFunctionSingularitiesInRectangle
                            χ hne
                            (primitiveReciprocalLowerCorner
                              hN2 hGRH hprimitive hne hinv hquad A k)
                            (primitiveReciprocalUpperCorner
                              hN2 hGRH hprimitive hne hinv hquad k)).erase
                        1).erase
                    0,
                dirichletReciprocalResidueAt hne
                  x ρ).re ≤
          ((1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
              (1 + 1 / x) * |primitiveBRe χ| -
              4 / 5) +
            2 * |primitiveBRe χ| /
              Real.sqrt x :=
        by
        have hbound' :
          (dirichletReciprocalResidueAt hne x
                  1).re +
              (dirichletReciprocalResidueAt hne
                  x 0).re ≤
            (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
              (1 + 1 / x) * |primitiveBRe χ| -
              4 / 5 := by
          simpa only [Complex.add_re, add_comm] using hbound.le
        exact add_le_add hbound' hsum
      _ =
          (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
            (1 - 1 / Real.sqrt x) ^ 2 *
              |primitiveBRe χ| :=
        by linear_combination hbcoeff
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletReciprocalContourKernel x
                χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletReciprocalContourKernel x χ
              (((primitiveReciprocalLeftRe A :
                    ℝ) :
                  ℂ) +
                (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`.
Conclusion:
`Re(R(x,χ)) ≤ (1/2)(1-1/x)(log N-log π) - 1/4 - (1-1/√x)²|Re B(χ)|`.
Content: `re_characterReciprocalWeightedSum_sub_leftVertical_le` holds for every `A ≥ 2`; the
subtracted term `(2π)⁻¹ Re(∫t,K(λ_A+it))` tends to `0` as `A → ∞` by
`DirichletLFunction.tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop`
(the analytic estimate's completion,
continuity of `Complex.re`); transferring through this limit via `le_of_tendsto` (restricted to the
eventual filter `A ≥ 2`) removes the left-vertical term entirely.
Role: the raw quadratic reciprocal-sum bound used by `PrimitiveQuadraticLemma23.lean`.
-/
theorem primitiveQuadraticReciprocalRaw {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
        (1 - 1 / Real.sqrt x) ^ 2 *
          |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) < x := by linarith
  have htend :=
    quadraticTendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop
      hprimitive hne hquad hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  simp only [Complex.zero_re] at htendRe
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel
                  x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re)
      Filter.atTop
      (nhds
        ((characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel
                  x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
          (1 - 1 / Real.sqrt x) ^ 2 *
            |primitiveBRe χ| := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterReciprocalWeightedSum_sub_leftVertical_le hN2 hGRH hprimitive hne hinv hquad hx A
        hA
  exact le_of_tendsto htendScaled hev

/-!
The strong even raw reciprocal estimate obtained from the `-4/5` main-error remainder.
It is deliberately an additional API, leaving the parity-uniform theorem above unchanged.
-/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem primitiveQuadraticReciprocalRaw_even_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (heven : χ.Even) {x : ℝ} (hx : 64 ≤ x) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
        (1 - 1 / Real.sqrt x) ^ 2 *
          |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) < x := by linarith
  have htend :=
    tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop
      hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  simp only [Complex.zero_re] at htendRe
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel
                  x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re)
      Filter.atTop
      (nhds
        ((characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel
                  x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
          (1 - 1 / Real.sqrt x) ^ 2 *
            |primitiveBRe χ| := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterReciprocalWeightedSum_sub_leftVertical_lt_of_even hN2 hGRH hprimitive hne hinv
        hquad heven hx A hA
  exact le_of_tendsto htendScaled hev

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, GRH, `x ≥ 64`.
Conclusion: `(1 - 1/√x)² |Re B(χ)| ≤ (1/2)(1 - 1/x) log(N/π) - Re(R(x,χ)) - 1/4`.
Content: thin polish wrapper over `primitiveQuadraticReciprocalRaw`, deriving `N ≥ 2` from `hne`
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one`)
and `χ⁻¹ ≠ 1` from `hquad` (`MulChar.IsQuadratic.inv`
collapses `χ⁻¹ = χ`), and converting `log N - log π` to `log(N/π)` via `Real.log_div`.
Role: the interface used by the level-indexed `PrimitiveQuadraticLemma23.lean` extension.
-/
theorem primitiveQuadraticReciprocalRaw' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x) :
    (1 - 1 / Real.sqrt x) ^ 2 *
        |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤
      (1 / 2) * (1 - 1 / x) * Real.log ((N : ℝ) / Real.pi) -
        (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re -
        1 / 4 := by
  have hN2 : 2 ≤ N := by
    have hN1 : N ≠ 1 :=
      AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
        hne
    have hNpos : 0 < N := NeZero.pos N
    omega
  have hinv : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]; exact hne
  have hraw := primitiveQuadraticReciprocalRaw hN2 hGRH hprimitive hne hinv hquad hx
  have hlogdiv : Real.log ((N : ℝ) / Real.pi) = Real.log N - Real.log Real.pi :=
    Real.log_div (by exact_mod_cast (NeZero.pos N).ne') Real.pi_ne_zero
  rw [hlogdiv]
  linarith [hraw]

end PseudoPrime.LLS.Extensions
