/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericHorizontalEdge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenResidueClosedForm
import PseudoPrime.LLS.PrimitiveReciprocalMainErrorBounds

/-! # Primitive reciprocal weighted-sum bounds under GRH

The common parity bound and two contour limits supply the reciprocal estimate
for the LLS comparison. The stronger even and quadratic specializations are separate.
-/

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`.
Conclusion: `Re (r₀ + r₁) ≤ (1/2)(1 - 1/x)(log N - log π) - (1 + 1/x)|Re B(χ)| - 1/4`.
Content: parity dispatch. Odd: (O)
(`DirichletLFunction.re_add_dirichletReciprocalResidues_zero_one_of_odd_raw`)
unfolds to the common term plus `PseudoPrime.Analysis.primitiveReciprocalOddMainError x`, bounded
by `-1/4`.
The even closed form uses the corresponding even main error. Quadraticity is not assumed.
Role: the parity-independent bound on `r₀ + r₁` used by `re_sum_llsPrimitiveReciprocalResidueAt_le`.
-/
theorem re_add_llsPrimitiveReciprocalResidues_zero_one_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) :
    (dirichletReciprocalResidueAt hne x 0 + dirichletReciprocalResidueAt hne x 1).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - (1 + 1 / x) * |primitiveBRe χ| -
        1 / 4 := by
  have hxpos : (0 : ℝ) < x := by linarith
  rcases χ.even_or_odd with heven | hodd
  · have hraw :=
      re_add_dirichletReciprocalResidues_zero_one_of_even_raw hN2 hGRH hprimitive hne hinv heven
        hxpos
    have herr := llsPrimitiveReciprocalEvenMainError_le_neg_quarter hx
    unfold Analysis.primitiveReciprocalEvenMainError at herr
    rw [hraw]
    nlinarith [herr]
  · have hraw :=
      re_add_dirichletReciprocalResidues_zero_one_of_odd_raw hN2 hGRH hprimitive hne hinv hodd hxpos
    have herr := llsPrimitiveReciprocalOddMainError_le_neg_quarter hx
    unfold Analysis.primitiveReciprocalOddMainError at herr
    rw [hraw]
    nlinarith [herr]

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial mod `N`, GRH, `χ⁻¹ ≠ 1`, `x ≥ 64`,
and a rectangle `z, w` whose primitive singularity ledger contains both Mellin points `0, 1`.
Quadraticity is not assumed. Conclusion:
`Re Σ_{s ∈ S} r(s) ≤ (1/2)(1 - 1/x)(log N - log π) - 1/4 - (1 - 1/√x)² |Re B(χ)|`.
Content:
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletSplitReciprocalSingularitySum` splits
`S`'s residue sum into `r₁ + r₀ +
(erased-ledger sum)`; `Complex.add_re` distributes the real part;
`re_add_llsPrimitiveReciprocalResidues_zero_one_le` bounds `r₀ + r₁`;
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.re_sum_erased_primitiveReciprocalResidues_le`
bounds the
erased-ledger sum by `2b/√x`; `-(1 + 1/x)b + 2b/√x = -(1 - 1/√x)²b` (`Real.sq_sqrt`, `ring`).
Role: an `A`, `k`-independent bound, ready for the fixed-`A`
`k → ∞` contour assembly.
-/
theorem re_sum_llsPrimitiveReciprocalResidueAt_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hx : 64 ≤ x) {z w : ℂ}
    (h0 :
      (0 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w)
    (h1 :
      (1 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne z
          w) :
    (∑
          s ∈
            AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ hne
              z w,
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x s).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
        (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  have hxpos : (0 : ℝ) < x := by linarith
  rw [AnalyticNumberTheory.DirichletLFunction.dirichletSplitReciprocalSingularitySum x hne h1 h0]
  have h01 := re_add_llsPrimitiveReciprocalResidues_zero_one_le hN2 hGRH hprimitive hne hinv hx
  have hzeros :=
    AnalyticNumberTheory.DirichletLFunction.re_sum_erased_primitiveReciprocalResidues_le hN2 hGRH
      hprimitive hne hinv hxpos (z := z) (w := w)
  have hsqrtx_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hinv_sqrt_sq : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [div_pow, one_pow, hsqrt_sq]
  have hbcoeff :
    -(1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
        2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| / Real.sqrt x =
      -(1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
    have hsqrtx_ne : Real.sqrt x ≠ 0 := hsqrtx_pos.ne'
    have hexpand : (1 - 1 / Real.sqrt x) ^ 2 = 1 - 2 / Real.sqrt x + 1 / x := by
      rw [sub_sq, one_pow, hinv_sqrt_sq]
      ring
    rw [hexpand]
    have h2sqrt : 2 / Real.sqrt x = 2 * (1 / Real.sqrt x) := by ring
    ring
  have herased_re :
    (∑
          ρ ∈
            ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle χ
                      hne z w).erase
                  1).erase
              0,
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x ρ).re ≤
      2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| / Real.sqrt x :=
    hzeros
  rw [Complex.add_re, Complex.add_re]
  calc
    (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 1).re +
          (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 0).re +
          (∑
              ρ ∈
                ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
                          χ hne z w).erase
                      1).erase
                  0,
              AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x ρ).re ≤
        ((1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
            (1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| -
            1 / 4) +
          2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| / Real.sqrt x :=
      by
      have h01' :
        (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 1).re +
            (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 0).re ≤
          (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
            (1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| -
            1 / 4 := by
        rw [add_comm]; rw [← Complex.add_re]; exact h01
      exact add_le_add h01' herased_re
    _ =
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
          (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| :=
      by linear_combination hbcoeff

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Generic reciprocal bound after taking the common-height contour limit. -/
theorem re_characterReciprocalWeightedSum_sub_leftVertical_le_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (characterReciprocalWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have htend :=
    tendsto_normalized_dirichletReciprocalBoundary_heightSeq_of_grh hN2 hGRH hprimitive hne hinv hx1
      A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletReciprocalContourKernel x χ)
              (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
          (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
    filter_upwards with k
    have hid :=
      dirichletReciprocalFiniteContourIdentity_heightSeq_normalized_of_grh hN2 hGRH hprimitive hne
        hinv (by linarith : (0 : ℝ) < x) A k hA
        (primitiveHeightSeq_singularities_mem_open_of_grh hN2 hGRH hprimitive hne hinv A k hA)
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq_of_grh hN2 hGRH hprimitive hne
        hinv A k hA
    have hbound :=
      re_sum_llsPrimitiveReciprocalResidueAt_le hN2 hGRH hprimitive hne hinv hx (z :=
        primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k) (w :=
        primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k) h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletReciprocalContourKernel x χ
              (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Generic reciprocal raw bound obtained by removing the left-vertical term with the `A → ∞`
limit. -/
theorem primitiveReciprocalRaw_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) < x := by linarith
  have htend :=
    tendsto_dirichletReciprocalContourKernel_leftVertical_integral_atTop hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  simp only [Complex.zero_re] at htendRe
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
      Filter.atTop (nhds ((characterReciprocalWeightedSum x χ).re - (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterReciprocalWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletReciprocalContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 1 / 4 -
          (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterReciprocalWeightedSum_sub_leftVertical_le_of_grh hN2 hGRH hprimitive hne hinv hx A
        hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.LLS
