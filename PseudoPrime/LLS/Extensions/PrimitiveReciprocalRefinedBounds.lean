/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds
public import PseudoPrime.LLS.Extensions.QNeOneNumerics
public import PseudoPrime.Analysis.LogarithmicMainTerms
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveContourRectangle
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenResidueClosedForm
public import PseudoPrime.Analysis.PrimitiveReciprocalMainErrorBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericHorizontalEdge

/-!
# Uniform upper bound for the finite reciprocal residue sum

Assembles the whole primitive singularity ledger's residue sum real-part bound, uniform in the
choice of rectangle (in particular `A`, `k`-independent): splits off `r₀ + r₁`
(`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletSplitReciprocalSingularitySum`),
bounds it by parity dispatch (the odd/even closed
forms plus the bounds in `LLS/PrimitiveReciprocalMainErrorBounds.lean`), and combines with the
erased-ledger zero-mass bound from `PrimitiveMultiplicityBridge.lean`.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-!
The even branch has a stronger remainder than the parity-uniform `-1/4` estimate.  This theorem
keeps that improvement separate so the existing generic raw API remains unchanged.
-/

/-- For an even primitive nonprincipal character under GRH and `x ≥ 64`, the combined
reciprocal residues at zero and one have the displayed strict upper bound with remainder
`-4/5`. Rewrite the even closed form and apply the stronger even main-error estimate.
This sharpens the parity-uniform residue input without requiring quadraticity. -/
theorem re_add_llsPrimitiveReciprocalResidues_zero_one_even_lt {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ}
    (hx : 64 ≤ x) :
    (AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 0 +
          AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalResidueAt hne x 1).re <
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
        (1 + 1 / x) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| -
        4 / 5 := by
  have hxpos : (0 : ℝ) < x := (by norm_num only : (0 : ℝ) < 64).trans_le hx
  have hraw :=
    AnalyticNumberTheory.DirichletLFunction.re_add_dirichletReciprocalResidues_zero_one_of_even_raw
      hN2 hGRH hprimitive hne hinv heven hxpos
  have herr := llsPrimitiveReciprocalEvenMainError_lt_neg_four_fifths hx
  unfold Analysis.primitiveReciprocalEvenMainError at herr
  rw [hraw]
  nlinarith only [herr]

/-! ### Fixed-`A`, `k → ∞` contour boundary limit -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an even primitive nonprincipal character under GRH, `x ≥ 64`, and
`A ≥ 2`, the fixed-left-edge reciprocal expression satisfies the displayed non-strict
bound with remainder `-4/5`. Split the residue ledger, complete the zero-mass square,
and pass to the height limit. The limiting conclusion is non-strict despite the name. -/
theorem re_characterReciprocalWeightedSum_sub_leftVertical_lt_of_even {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ} (hx : 64 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    (characterReciprocalWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletReciprocalContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) ≤ x := (by norm_num only : (1 : ℝ) ≤ 64).trans hx
  have htend :=
    tendsto_normalized_dirichletReciprocalBoundary_heightSeq hN2 hGRH hprimitive hne hinv hx1 A hA
  have htendRe := (Complex.continuous_re.tendsto _).comp htend
  have hev :
    ∀ᶠ k : ℕ in Filter.atTop,
      ((-Complex.I / (2 * (Real.pi : ℂ))) *
            AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
              (dirichletReciprocalContourKernel x χ)
              (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
              (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)).re ≤
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
          (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
    filter_upwards with k
    have hid :=
      dirichletReciprocalFiniteContourIdentity_heightSeq_normalized hN2 hGRH hprimitive hne hinv
        (show (0 : ℝ) < x from (by norm_num only : (0 : ℝ) < 64).trans_le hx) A k hA
        (primitiveHeightSeq_singularities_mem_open hN2 hGRH hprimitive hne hinv A k hA)
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq hN2 hGRH hprimitive hne hinv A k
        hA
    have hbound :=
      re_add_llsPrimitiveReciprocalResidues_zero_one_even_lt hN2 hGRH hprimitive hne hinv heven hx
    rw [hid]
    have hsum :=
      re_sum_erased_primitiveReciprocalResidues_le hN2 hGRH hprimitive hne hinv
        (show (0 : ℝ) < x from (by norm_num only : (0 : ℝ) < 64).trans_le hx) (z :=
        primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k) (w :=
        primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)
    rw [dirichletSplitReciprocalSingularitySum x hne h1 h0]
    rw [Complex.add_re, Complex.add_re]
    have hsqrtx_pos : (0 : ℝ) < Real.sqrt x :=
      Real.sqrt_pos.mpr ((by norm_num only : (0 : ℝ) < 64).trans_le hx)
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt ((by norm_num only : (0 : ℝ) ≤ 64).trans hx)
    have hinv_sqrt_sq : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [div_pow, one_pow, hsqrt_sq]
    have hbcoeff :
      -(1 + 1 / x) * |primitiveBRe χ| + 2 * |primitiveBRe χ| / Real.sqrt x =
        -(1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
      have hsqrtx_ne : Real.sqrt x ≠ 0 := hsqrtx_pos.ne'
      have hexpand : (1 - 1 / Real.sqrt x) ^ 2 = 1 - 2 / Real.sqrt x + 1 / x := by
        rw [sub_sq, one_pow, hinv_sqrt_sq]
        ring
      rw [hexpand]
      ring
    calc
      (dirichletReciprocalResidueAt hne x 1).re + (dirichletReciprocalResidueAt hne x 0).re +
            (∑
                ρ ∈
                  ((dirichletLFunctionSingularitiesInRectangle χ hne
                            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
                            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)).erase
                        1).erase
                    0,
                dirichletReciprocalResidueAt hne x ρ).re ≤
          ((1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
              (1 + 1 / x) * |primitiveBRe χ| -
              4 / 5) +
            2 * |primitiveBRe χ| / Real.sqrt x :=
        by
        have hbound' :
          (dirichletReciprocalResidueAt hne x 1).re + (dirichletReciprocalResidueAt hne x 0).re ≤
            (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
              (1 + 1 / x) * |primitiveBRe χ| -
              4 / 5 := by
          simpa only [Complex.add_re, add_comm] using hbound.le
        exact add_le_add hbound' hsum
      _ =
          (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
            (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| :=
        by linear_combination hbcoeff
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
        push_cast
        ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The reciprocal weighted-sum upper bound with remainder `-4/5` for an even primitive
nonprincipal character under GRH and `x ≥ 64`.
Send the left edge to minus infinity in the stronger fixed-edge estimate, using vanishing
of its whole-line integral. This retains the even improvement in the raw reciprocal estimate. -/
theorem primitiveReciprocalRaw_even_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ} (hx : 64 ≤ x) :
    (characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
        (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
  have hx1 : (1 : ℝ) < x := (by norm_num only : (1 : ℝ) < 64).trans_le hx
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
        (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 4 / 5 -
          (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ| := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact
      re_characterReciprocalWeightedSum_sub_leftVertical_lt_of_even hN2 hGRH hprimitive hne hinv
        heven hx A hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.LLS.Extensions
