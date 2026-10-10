/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicMainTerms
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues

/-!
# Logarithmic weighted-sum estimates with the exact even main term

The residue ledger and two contour limits retain
`primitiveLogEvenMainError x = π²/24 - (γ/2) log x - (log x)²/2` explicitly.
The regularized local-factor identity at a square radius is also provided. No numerical
relaxation of the even main term is used. The weighted-sum estimates assume GRH, a primitive
nontrivial even character, and `x ≥ 64`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: the generic residue ledger hypotheses, with an even primitive
character and `x ≥ 64`.
Conclusion: the residue sum is bounded by the zero-mass and conductor terms plus
`π²/24 - (γ/2) log x - (log x)²/2`.
Content: use the raw even zero-residue formula together with the completed-L derivative bound,
then add the unchanged erased-zero ledger estimate.
Role: refined residue input for the even square-radius upper bound.
-/
theorem re_sum_dirichletLogResidueAt_le_of_grh_even_exact {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ}
    (hx : 64 ≤ x) {z w : ℂ} (h0 : (0 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w)
    (h1 : (1 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w) :
    (∑ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w, dirichletLogResidueAt hne x s).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
        (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        Analysis.primitiveLogEvenMainError x := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx
  rw [dirichletSplitLogSingularitySum x hne h1 h0, dirichletLogResidueAt_one hne x]
  have hr0_bound :
    (dirichletLogResidueAt hne x 0).re ≤
      (2 + Real.log x) * |primitiveBRe χ| + (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        Analysis.primitiveLogEvenMainError x := by
    rw [dirichletLogResidueAt_zero_of_even hne x heven]
    rw [re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two hN2 hGRH hprimitive hne
        hinv hxpos]
    have hD := neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe hGRH hprimitive hne hinv hN2
    have hlogx_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (le_trans (by norm_num only) hx)
    unfold Analysis.primitiveLogEvenMainError
    have hstep :
      -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
          |primitiveBRe χ| * Real.log x ≤
        2 * |primitiveBRe χ| + |primitiveBRe χ| * Real.log x :=
      add_le_add hD (le_refl _)
    calc
      _ =
          (-(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
              |primitiveBRe χ| * Real.log x) +
            ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
              (Real.pi ^ 2 / 24 - Real.eulerMascheroniConstant / 2 * Real.log x -
                1 / 2 * Real.log x ^ 2)) :=
        by ring
      _ ≤
          (2 * |primitiveBRe χ| + |primitiveBRe χ| * Real.log x) +
            ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
              (Real.pi ^ 2 / 24 - Real.eulerMascheroniConstant / 2 * Real.log x -
                1 / 2 * Real.log x ^ 2)) :=
        add_le_add hstep (le_refl _)
      _ = _ := by ring
  have herased :=
    re_sum_erased_primitiveLogResidues_le hN2 hGRH hprimitive hne hinv hxpos (z := z) (w := w)
  simp only [Complex.add_re, Complex.zero_re]
  have hsum := add_le_add hr0_bound herased
  calc
    0 + (dirichletLogResidueAt hne x 0).re +
          (∑ ρ ∈ ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0,
              dirichletLogResidueAt hne x ρ).re =
        (dirichletLogResidueAt hne x 0).re +
          (∑ ρ ∈ ((dirichletLFunctionSingularitiesInRectangle χ hne z w).erase 1).erase 0,
              dirichletLogResidueAt hne x ρ).re :=
      by rw [zero_add]
    _ ≤
        (2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          Analysis.primitiveLogEvenMainError x +
          2 * Real.sqrt x * |primitiveBRe χ| :=
      hsum
    _ =
        (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          Analysis.primitiveLogEvenMainError x :=
      by ring

/-- Fixed-`A` contour bound retaining the even main-error term. -/
theorem re_characterLogWeightedSum_sub_leftVertical_le_even_exact {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ}
    (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (Arithmetic.characterLogWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
        (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        Analysis.primitiveLogEvenMainError x := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have htend :=
    tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh hN2 hGRH hprimitive hne hinv hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
              (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          Analysis.primitiveLogEvenMainError x := by
    filter_upwards with k
    have hid :=
      dirichletLogFiniteContourIdentity_heightSeq_normalized hN2 hGRH hprimitive hne hinv
        (lt_of_lt_of_le (by norm_num only) hx) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq hN2 hGRH hprimitive hne hinv A k
        hA
    have hbound :=
      re_sum_dirichletLogResidueAt_le_of_grh_even_exact hN2 hGRH hprimitive hne hinv heven hx (z :=
        primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k) (w :=
        primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) h0 h1
    rw [hid]
    exact hbound
  have hlimit := le_of_tendsto htendRe hev
  rw [Complex.sub_re] at hlimit
  have hmulre :
    ((↑(2 * Real.pi))⁻¹ *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I) :
          ℂ).re =
      (2 * Real.pi)⁻¹ *
        (∫ t : ℝ,
            dirichletLogContourKernel x χ
              (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/-- Whole-line logarithmic upper bound retaining the even main-error term. -/
theorem primitiveLogWeightedUpper_of_grh_even_exact {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ}
    (hx : 64 ≤ x) :
    (Arithmetic.characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
        (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        Analysis.primitiveLogEvenMainError x := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
  have htend :=
    tendsto_dirichletLogContourKernel_leftVertical_integral_atTop hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (Arithmetic.characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
      Filter.atTop (nhds ((Arithmetic.characterLogWeightedSum x χ).re - (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (Arithmetic.characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          Analysis.primitiveLogEvenMainError x := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterLogWeightedSum_sub_leftVertical_le_even_exact hN2 hGRH hprimitive hne hinv heven
        hx A hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
