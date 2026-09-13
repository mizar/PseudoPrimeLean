/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
import PseudoPrime.LLS.PrimitiveLogMainErrorBounds

/-! # Primitive logarithmic weighted-sum bounds under GRH

The parity-independent residue estimate and the contour limits give the logarithmic
upper bound used in the common LLS comparison. No quadraticity hypothesis is imposed.
-/

namespace PseudoPrime.LLS

/-! The generic even-zero closed form with its explicit `x ≥ 64` upper bound. -/

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem re_iteratedDeriv_two_llsPrimitiveLogEvenZeroRegularization_zero_div_two_le_of_grh {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) :
    (iteratedDeriv 2
            (dirichletLogEvenZeroRegularization
              x 1
              (dirichletEvenZeroLocalFactor χ))
            0 /
          2).re ≤
      (2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  rw [re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_of_grh
      hN2 hGRH hprimitive hne hinv
      (show (0 : ℝ) < x from lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx)]
  have hD :=
    neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe_of_grh
      hGRH hprimitive hne hinv hN2
  have hE := llsPrimitiveLogEvenMainError_le_neg_eleven_fourths hx
  unfold Analysis.primitiveLogEvenMainError at hE
  have hsum := add_le_add hD hE
  calc
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            |primitiveBRe χ| * Real.log x +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            Real.pi ^ 2 / 24 -
          (Real.eulerMascheroniConstant / 2) * Real.log x -
          (1 / 2) * (Real.log x) ^ 2 =
        (-(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            (Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log x -
              (1 / 2) * (Real.log x) ^ 2)) +
          ((1 / 2) * (Real.log ↑N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by ring
    _ ≤
        (2 * |primitiveBRe χ| + (-(11 / 4))) +
          ((1 / 2) * (Real.log ↑N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by
      have h :=
        add_le_add hsum
          (le_refl
            ((1 / 2) * (Real.log ↑N - Real.log Real.pi) * Real.log x +
              |primitiveBRe χ| * Real.log x))
      exact h
    _ =
        (2 + Real.log x) * |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 :=
      by ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem re_deriv_llsPrimitiveLogMellinZeroRegularization_zero_of_odd_le_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hodd : χ.Odd) {x : ℝ}
    (hx : 64 ≤ x) :
    (deriv
          (dirichletLogMellinZeroRegularization
            x χ)
          0).re ≤
      (2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  rw [re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd_of_grh
      hN2 hGRH hprimitive hne hinv hodd
      (show (0 : ℝ) < x from lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx)]
  have hD :=
    neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe_of_grh
      hGRH hprimitive hne hinv hN2
  have hE := llsPrimitiveLogOddMainError_le_neg_eleven_fourths hx
  unfold Analysis.primitiveLogOddMainError at hE
  have hsum := add_le_add hD hE
  calc
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            |primitiveBRe χ| * Real.log x +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            Real.pi ^ 2 / 8 -
          (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x =
        (-(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            (Real.pi ^ 2 / 8 - (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x)) +
          ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by ring
    _ ≤
        (2 * |primitiveBRe χ| + (-(11 / 4))) +
          ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by
      have h :=
        add_le_add hsum
          (le_refl
            ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
              |primitiveBRe χ| * Real.log x))
      exact h
    _ =
        (2 + Real.log x) * |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 :=
      by ring

/-! The full generic residue ledger, after replacing both zero branch and erased ledger bounds. -/

theorem re_sum_llsPrimitiveLogResidueAt_le_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) {z w : ℂ}
    (h0 :
      (0 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
          χ hne z w)
    (h1 :
      (1 : ℂ) ∈
        AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
          χ hne z w) :
    (∑
          s ∈
            AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
              χ hne z w,
          AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x s).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx
  rw [AnalyticNumberTheory.DirichletLFunction.dirichletSplitLogSingularitySum x hne h1
      h0,
    AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_one hne x]
  have hr0_bound :
    (AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 0).re ≤
      (2 + Real.log x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
    rcases χ.even_or_odd with heven | hodd
    · rw [AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_zero_of_even hne
          x heven]
      exact
        re_iteratedDeriv_two_llsPrimitiveLogEvenZeroRegularization_zero_div_two_le_of_grh hN2 hGRH
          hprimitive hne hinv hx
    · rw [AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt_zero_of_odd hne
          x hodd]
      exact
        re_deriv_llsPrimitiveLogMellinZeroRegularization_zero_of_odd_le_of_grh hN2 hGRH hprimitive
          hne hinv hodd hx
  have herased :=
    AnalyticNumberTheory.DirichletLFunction.re_sum_erased_primitiveLogResidues_le_of_grh
      hN2 hGRH hprimitive hne hinv hxpos (z := z) (w := w)
  simp only [Complex.add_re, Complex.zero_re]
  have hsum := add_le_add hr0_bound herased
  calc
    0 + (AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 0).re +
          (∑
              ρ ∈
                ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
                          χ hne z w).erase
                      1).erase
                  0,
              AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x
                ρ).re =
        (AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x 0).re +
          (∑
              ρ ∈
                ((AnalyticNumberTheory.DirichletLFunction.dirichletLFunctionSingularitiesInRectangle
                          χ hne z w).erase
                      1).erase
                  0,
              AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt hne x
                ρ).re :=
      by rw [zero_add]
    _ ≤
        (2 + Real.log x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
              (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
            11 / 4 +
          2 * Real.sqrt x * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| :=
      hsum
    _ =
        (2 * Real.sqrt x + 2 + Real.log x) *
              |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 :=
      by ring

/-! Generic fixed-`A` bound obtained from the residue ledger. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem re_characterLogWeightedSum_sub_leftVertical_le_generic_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) (A : ℕ)
    (hA : 2 ≤ A) :
    (characterLogWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I)).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have htend :=
    tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh
      hN2 hGRH hprimitive hne hinv hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletLogContourKernel x χ)
              (primitiveHeightSeqLowerCorner_of_grh
                hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner_of_grh
                hN2 hGRH hprimitive hne hinv k)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) *
              |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards with k
    have hid :=
      dirichletLogFiniteContourIdentity_heightSeq_normalized_of_grh
        hN2 hGRH hprimitive hne hinv (lt_of_lt_of_le (by norm_num only) hx) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq_of_grh
        hN2 hGRH hprimitive hne hinv A k hA
    have hbound :=
      re_sum_llsPrimitiveLogResidueAt_le_of_grh hN2 hGRH hprimitive hne hinv hx (z :=
        primitiveHeightSeqLowerCorner_of_grh hN2
          hGRH hprimitive hne hinv A k)
        (w :=
        primitiveHeightSeqUpperCorner_of_grh hN2
          hGRH hprimitive hne hinv k)
        h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A :
                      ℝ) :
                    ℂ) +
                  (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletLogContourKernel x χ
              (((primitiveReciprocalLeftRe A :
                    ℝ) :
                  ℂ) +
                (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/-! Generic logarithmic raw bound obtained by removing the left edge. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
theorem primitiveGenericLogWeightedUpper_of_grh_generic {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) :
    (characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
  have htend :=
    tendsto_dirichletLogContourKernel_leftVertical_integral_atTop
      hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re)
      Filter.atTop
      (nhds
        ((characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe
                          A :
                        ℝ) :
                      ℂ) +
                    (t : ℂ) * Complex.I)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) *
              |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterLogWeightedSum_sub_leftVertical_le_generic_of_grh hN2 hGRH hprimitive hne hinv hx
        A hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.LLS
