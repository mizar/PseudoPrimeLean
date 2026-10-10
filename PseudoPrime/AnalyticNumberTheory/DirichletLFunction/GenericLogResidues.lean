/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogContourRectangle

/-! Generic GRH boundary limits and exact logarithmic residue identities. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: generic GRH height data, a primitive nontrivial character, `x ≥ 1`, and `A ≥ 2`.
Conclusion: the normalized generic logarithmic rectangle boundary converges along the height
sequence to the character log-weighted sum minus the left-vertical whole-line integral.
Content: expand the four rectangle edges, then combine generic horizontal decay, right-edge
interval exhaustion, and the generic left-vertical height-sequence limit.
Role: fixed-`A` normalized boundary interface for the generic logarithmic raw bound.
-/
theorem tendsto_normalized_dirichletLogBoundary_heightSeq_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (A : ℕ)
    (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k))
      Filter.atTop
      (nhds
        (Arithmetic.characterLogWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hcoeffI : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]
        ring]
    push_cast
    ring
  have heq :
    ∀ k : ℕ,
      (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) =
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    intro k
    obtain ⟨hzre, hzim, hwre, hwim, _, _⟩ :=
      primitiveHeightSeqRectangleFacts hN2 hGRH hprimitive hne hinv A k hA
    unfold RectangleGeometry.rectangleBoundaryIntegral
    rw [hzre, hzim, hwre, hwim, primitiveReciprocalLeftRe]
    simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul]
    linear_combination
      (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
            dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI -
        (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
            dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI
  apply Filter.Tendsto.congr (fun k => (heq k).symm)
  have hhoriz :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_horizontal_integral A hA hN2 hGRH hprimitive hne
      hinv hx
  have hright :=
    (tendsto_intervalIntegral_dirichletLogContourKernel hxpos χ hne
          (show (1 : ℝ) < 2 by norm_num only)).comp
      (tendsto_primitiveHorizontalHeightSeq_atTop hN2 hGRH hprimitive hne hinv)
  have hleft :=
    tendsto_primitiveHorizontalHeightSeq_log_leftVertical_intervalIntegral hN2 hGRH hprimitive hne
      hinv hxpos hA
  have hweighted := characterLogWeightedSum_eq_integral χ hxpos (show (1 : ℝ) < 2 by norm_num only)
  have htarget :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (nhds
        ((-Complex.I / (2 * (Real.pi : ℂ))) * ((0 : ℂ) - 0) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t : ℝ, dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    apply Filter.Tendsto.sub
    · apply Filter.Tendsto.add
      · exact Filter.Tendsto.const_mul _ (hhoriz.2.sub hhoriz.1)
      · exact Filter.Tendsto.const_mul _ hright
    · exact Filter.Tendsto.const_mul _ hleft
  simp only [sub_zero, mul_zero, zero_add] at htarget
  rw [hweighted, Complex.real_smul]
  convert htarget using 2
  push_cast
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
