/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GenericLogResidues
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
public import PseudoPrime.LLS.PrimitiveLogMainErrorBounds
public import PseudoPrime.LLS.PrimitiveLogResidueLedger

/-! # Primitive logarithmic weighted-sum bounds under GRH

The parity-independent residue estimate and the contour limits give the logarithmic
upper bound used in the common LLS comparison. No quadraticity hypothesis is imposed.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-! Generic fixed-`A` bound obtained from the residue ledger. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For `A ≥ 2`, bound the real logarithmic weighted sum after subtracting the normalized
left vertical integral, assuming GRH, primitivity, nonprincipality, and `x ≥ 64`.
Apply the residue bound to every rectangle in the common height sequence and pass to
the boundary-integral limit. This retains the left edge for its subsequent removal. -/
theorem re_characterLogWeightedSum_sub_leftVertical_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) (A : ℕ)
    (hA : 2 ≤ A) :
    (characterLogWeightedSum x χ).re -
        (2 * Real.pi)⁻¹ *
          (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num only) hx
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
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards with k
    have hid :=
      dirichletLogFiniteContourIdentity_heightSeq_normalized hN2 hGRH hprimitive hne hinv
        (lt_of_lt_of_le (by norm_num only) hx) A k hA
    obtain ⟨h0, h1⟩ :=
      primitiveReciprocalMellinPoints_mem_singularities_heightSeq hN2 hGRH hprimitive hne hinv A k
        hA
    have hbound :=
      re_sum_llsPrimitiveLogResidueAt_le hN2 hGRH hprimitive hne hinv hx (z :=
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
        push_cast
        ring,
      Complex.re_ofReal_mul]
  rw [hmulre] at hlimit
  exact hlimit

/-! Generic logarithmic raw bound obtained by removing the left edge. -/

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- The logarithmic weighted-sum upper bound for a primitive nonprincipal character under
GRH and `x ≥ 64`, with no quadraticity or parity restriction.
The fixed-left-edge inequality passes to the limit as `A → ∞`, where the left vertical
integral tends to zero. This provides the generic logarithmic input to LLS comparison. -/
theorem primitiveGenericLogWeightedUpper {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) :
    (characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num only) hx
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
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with A hA
    exact re_characterLogWeightedSum_sub_leftVertical_le hN2 hGRH hprimitive hne hinv hx A hA
  exact le_of_tendsto htendScaled hev

end PseudoPrime.LLS
