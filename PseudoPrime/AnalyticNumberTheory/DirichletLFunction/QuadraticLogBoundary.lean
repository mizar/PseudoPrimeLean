/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveQuadraticLogLeftVertical
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogExplicitFormula
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogHorizontalEdge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveGenericLogLeftVertical
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogContourRectangle

/-! General smoothed-contour identities and bounds. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
For `N ≥ 2`, a primitive nontrivial quadratic character with nontrivial inverse,
GRH, `x ≥ 1`, and `A ≥ 2`, the normalized logarithmic boundary integral converges
to the weighted character sum minus `(2π)⁻¹` times the whole left-line integral.
The horizontal integrals vanish; the right real-parameter integral tends to `2π*S(x,χ)`,
and the left one tends to its whole-line integral. The vertical orientation factors
and `-i/(2π)` give the displayed normalization.
-/
theorem tendsto_normalized_dirichletLogBoundary_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 1 ≤ x) (A : ℕ) (hA : 2 ≤ A) :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k))
      Filter.atTop
      (nhds
        (Arithmetic.characterLogWeightedSum x χ -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            ∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hpi_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have hpine : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, hpine, or_self,
      not_false_eq_true]
  have hcoeffI : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]; ring]
    push_cast; ring
  have heq :
    ∀ k : ℕ,
      (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) =
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
    intro k
    have hzre :
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).re =
        primitiveReciprocalLeftRe A := by
      rw [primitiveReciprocalLowerCorner]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
    have hzim :
      (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k).im =
        -(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k) := by
      rw [primitiveReciprocalLowerCorner]
      simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]
    have hwre : (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).re = 2 := by
      rw [primitiveReciprocalUpperCorner]
      simp only [Complex.ofReal_ofNat, Complex.add_re, Complex.re_ofNat, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one,
        sub_self, add_zero]
    have hwim :
      (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k).im =
        primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k := by
      rw [primitiveReciprocalUpperCorner]
      simp only [Complex.ofReal_ofNat, Complex.add_im, Complex.im_ofNat, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
        add_zero, zero_add]
    unfold RectangleGeometry.rectangleBoundaryIntegral
    rw [hzre, hzim, hwre, hwim, primitiveReciprocalLeftRe]
    simp only [smul_eq_mul, Complex.ofReal_neg, neg_mul]
    linear_combination
      (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
            dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI -
        (∫ t in
            (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
            dirichletLogContourKernel x χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
          hcoeffI
  apply Filter.Tendsto.congr (fun k => (heq k).symm)
  have hhoriz :=
    tendsto_primitiveHorizontalHeightSeq_logKernel_horizontal_integral A hA hN2 hGRH hprimitive hne
      hinv hquad hx
  have hright :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ t in
          (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
              k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
          dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (nhds (∫ t : ℝ, dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I))) :=
    (tendsto_intervalIntegral_dirichletLogContourKernel hxpos χ hne
          (show (1 : ℝ) < 2 from by norm_num only)).comp
      (tendsto_primitiveHorizontalHeightSeq_atTop hN2 hGRH hprimitive hne hinv hquad)
  have hleft :=
    quadraticTendsto_primitiveHorizontalHeightSeq_log_leftVertical_intervalIntegral hN2 hGRH
      hprimitive hne hinv hquad hxpos hA
  have hweighted :=
    characterLogWeightedSum_eq_integral χ hxpos (show (1 : ℝ) < 2 from by norm_num only)
  have htarget :
    Filter.Tendsto
      (fun k : ℕ =>
        (-Complex.I / (2 * (Real.pi : ℂ))) *
              ((∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) -
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) -
                ∫ σ in (-(A : ℝ) - 1 / 2)..(2 : ℝ),
                  dirichletLogContourKernel x χ
                    ((σ : ℂ) +
                      primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k *
                        Complex.I)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t in
                (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                    k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
                dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t in
              (-(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad
                  k))..(primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv hquad k),
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop
      (nhds
        ((-Complex.I / (2 * (Real.pi : ℂ))) * ((0 : ℂ) - (0 : ℂ)) +
            ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
              (∫ t : ℝ, dirichletLogContourKernel x χ ((2 : ℂ) + (t : ℂ) * Complex.I)) -
          ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ t : ℝ,
              dirichletLogContourKernel x χ
                (((primitiveReciprocalLeftRe A : ℝ) : ℂ) + (t : ℂ) * Complex.I)))) := by
    apply Filter.Tendsto.sub
    · apply Filter.Tendsto.add
      · exact (Filter.Tendsto.const_mul _ (hhoriz.2.sub hhoriz.1))
      · exact Filter.Tendsto.const_mul _ hright
    · exact Filter.Tendsto.const_mul _ hleft
  simp only [sub_zero, mul_zero, zero_add] at htarget
  rw [hweighted, Complex.real_smul]
  convert htarget using 2
  push_cast; ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
