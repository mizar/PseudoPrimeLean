/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveLogWeightedBounds

/-! # Logarithmic weighted bounds with a parameterized main error -/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For positive x and a primitive nonprincipal character under GRH,
bounds by e for both parity main errors give the origin-residue estimate.
Combine the exact closed forms with the completed logarithmic derivative bound.
This retains the numerical error instead of fixing a cutoff at 64. -/
theorem primitiveLogOrigin_le_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x e : ℝ} (hx : 0 < x)
    (ho : Analysis.primitiveLogOddMainError x ≤ e) (he : Analysis.primitiveLogEvenMainError x ≤ e) :
    (dirichletLogResidueAt hne x 0).re ≤
      (2 + Real.log x) * |primitiveBRe χ| + (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        e := by
  have hD := neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe hGRH hprimitive hne hinv hN2
  rcases χ.even_or_odd with heven | hodd
  · rw [dirichletLogResidueAt_zero_of_even hne x heven,
      re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two hN2 hGRH hprimitive hne
        hinv hx]
    unfold Analysis.primitiveLogEvenMainError at he
    linarith only [hD, he]
  · rw [dirichletLogResidueAt_zero_of_odd hne x hodd,
      re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd hN2 hGRH hprimitive hne hinv hodd
        hx]
    unfold Analysis.primitiveLogOddMainError at ho
    linarith only [hD, ho]

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For positive x and rectangles containing zero and one, the two
parity main-error bounds by e control the complete logarithmic residue ledger.
Add the origin bound to the finite zero contribution. This supplies the
finite-contour input for any numerically admissible cutoff. -/
theorem primitiveLogLedger_le_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x e : ℝ} (hx : 0 < x)
    (ho : Analysis.primitiveLogOddMainError x ≤ e) (he : Analysis.primitiveLogEvenMainError x ≤ e)
    {z w : ℂ} (h0 : (0 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w)
    (h1 : (1 : ℂ) ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w) :
    (∑ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w, dirichletLogResidueAt hne x s).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
        (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        e := by
  have hzero := primitiveLogOrigin_le_of_mainErrors hN2 hGRH hprimitive hne hinv hx ho he
  have hrest :=
    re_sum_erased_primitiveLogResidues_le hN2 hGRH hprimitive hne hinv hx (z := z) (w := w)
  rw [dirichletSplitLogSingularitySum x hne h1 h0, dirichletLogResidueAt_one hne x]
  simp only [Complex.add_re, Complex.zero_re]
  nlinarith only [hzero, hrest]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one and A at least two, bounds by e for both
parity main errors give the weighted-sum estimate with its left edge retained.
Pass the parameterized finite-ledger inequality through the common-height
contour limit. This separates analytic convergence from numerical cutoffs. -/
theorem characterLogWeightedSum_sub_leftVertical_le_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x e : ℝ} (hx : 1 < x)
    (ho : Analysis.primitiveLogOddMainError x ≤ e) (he : Analysis.primitiveLogEvenMainError x ≤ e)
    (A : ℕ) (hA : 2 ≤ A) :
    (characterLogWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
        (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        e := by
  have hx1 : (1 : ℝ) ≤ x := hx.le
  have htend :=
    tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh hN2 hGRH hprimitive hne hinv hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletLogContourKernel x χ)
              (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          e := by
    filter_upwards with k
    have hid :=
      dirichletLogFiniteContourIdentity_heightSeq_normalized hN2 hGRH hprimitive hne hinv
        (zero_lt_one.trans hx) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq hN2 hGRH hprimitive hne hinv A k
        hA
    have hbound :=
      primitiveLogLedger_le_of_mainErrors hN2 hGRH hprimitive hne hinv (zero_lt_one.trans hx) ho he
        (z := primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k) (w :=
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
    rw [show ((↑(2 * Real.pi))⁻¹ : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) from
        (Complex.ofReal_inv (2 * Real.pi)).symm,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/-! Generic logarithmic raw bound obtained by removing the left edge. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For x greater than one and both parity main errors at most e,
a primitive nonprincipal character under GRH satisfies the displayed sum bound.
Remove the left edge by its existing limit as A tends to infinity.
This is the cutoff-independent logarithmic input for witness comparisons. -/
theorem primitiveLogWeightedUpper_of_mainErrors {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x e : ℝ} (hx : 1 < x)
    (ho : Analysis.primitiveLogOddMainError x ≤ e) (he : Analysis.primitiveLogEvenMainError x ≤ e) :
    (characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
        (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
        e := by
  have hx1 : (1 : ℝ) < x := hx
  have htend :=
    tendsto_dirichletLogContourKernel_leftVertical_integral_atTop hprimitive hne hinv hx1
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have htendScaled :
    Filter.Tendsto
      (fun A : ℕ =>
        (characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
      Filter.atTop (nhds ((characterLogWeightedSum x χ).re - (2 * Real.pi)⁻¹ * 0)) :=
    Filter.Tendsto.const_sub _ (Filter.Tendsto.const_mul _ htendRe)
  simp only [mul_zero, sub_zero] at htendScaled
  have hev :
    ∀ᶠ A : ℕ in Filter.atTop,
      (characterLogWeightedSum x χ).re -
          (2 * Real.pi)⁻¹ *
            (∫ t : ℝ,
                dirichletLogContourKernel x χ
                  (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
        (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
          e := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      characterLogWeightedSum_sub_leftVertical_le_of_mainErrors hN2 hGRH hprimitive hne hinv hx ho
        he A hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.LLS
