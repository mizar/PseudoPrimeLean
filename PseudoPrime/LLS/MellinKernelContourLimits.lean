/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelFiniteContour
public import PseudoPrime.LLS.MellinKernelHorizontal
public import PseudoPrime.LLS.MellinKernelVerticalIntegrability
public import PseudoPrime.LLS.MellinKernelContourGeometry

/-!
# Good-height limits for weighted completed contours

The concrete completed logarithmic derivative has vanishing horizontal contributions.
When both vertical lines are integrable, the rectangle boundaries converge to their difference.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data and a positive scale at least one, the completed
weighted rectangle boundaries along good heights converge to the difference of vertical
integrals. The horizontal interval lies in the kernel strip and the fixed completed strip;
absolute integrability of both vertical lines is assumed explicitly.
The proof removes both horizontal edges using the good-height estimate and applies the
improper integral limit. This connects finite residues with the remaining vertical estimates. -/
theorem tendsto_completed_boundaryIntegral (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a ≤ b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -5 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x)
    (hleft :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          -logDeriv χ.completedLFunction (((a : ℂ) + t * Complex.I) + 1 / 2) *
            (K.function ((a : ℂ) + t * Complex.I) * (x : ℂ) ^ ((a : ℂ) + t * Complex.I))))
    (hright :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          -logDeriv χ.completedLFunction (((b : ℂ) + t * Complex.I) + 1 / 2) *
            (K.function ((b : ℂ) + t * Complex.I) * (x : ℂ) ^ ((b : ℂ) + t * Complex.I)))) :
    let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv
    let F := fun s : ℂ => -logDeriv χ.completedLFunction (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)
    Filter.Tendsto
      (fun n =>
        AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F
          ((a : ℂ) - T n * Complex.I) ((b : ℂ) + T n * Complex.I))
      Filter.atTop
      (nhds
        (Complex.I *
          ((∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) - (∫ t : ℝ, F ((a : ℂ) + t * Complex.I))))) := by
  apply
    AnalyticNumberTheory.RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits _
      (tendsto_primitiveHorizontalHeightSeq_atTop hq hGRH hp hne hinv)
  · have h :=
      (tendsto_completed_horizontalIntegral K hq hGRH hp hne hinv hab ha hb ha' hb' hx (-1)
          (Or.inr rfl)).neg
    simpa only [neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul, mul_assoc,
      intervalIntegral.integral_neg, neg_zero] using h
  · have h :=
      (tendsto_completed_horizontalIntegral K hq hGRH hp hne hinv hab ha hb ha' hb' hx 1
          (Or.inl rfl)).neg
    simpa only [one_mul, neg_mul, mul_assoc, intervalIntegral.integral_neg, neg_zero] using h
  · exact hleft
  · exact hright

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH data and a positive scale at least one, the weighted
finite residue sum along good heights converges to the difference of vertical integrals
multiplied by `i`. Choose ordered lines in the kernel strip, with the left line between
-3/2 and -1/2 and the right line between 1/2 and 3/2.
Proved logarithmic bounds give both vertical integrals; GRH and good-height nonvanishing
put the entire finite ledger in the rectangle interior. The finite residue identity and
vanishing horizontal edges then identify the limit, with no additional analytic certificates. -/
theorem tendsto_completed_residueSum (K : MellinKernel) {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - K.delta < a) (hb : b ≤ 1 / 2 + K.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (haleft : a < -1 / 2) (hbright : 1 / 2 < b) :
    let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv
    let F := fun s : ℂ => -logDeriv χ.completedLFunction (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)
    Filter.Tendsto
      (fun n =>
        ∑
          s ∈
            completedKernelSingularities hp hne ((a : ℂ) - T n * Complex.I)
              ((b : ℂ) + T n * Complex.I),
          2 * Real.pi * Complex.I *
            weightedResidue K (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) x s)
      Filter.atTop
      (nhds
        (Complex.I *
          ((∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) - (∫ t : ℝ, F ((a : ℂ) + t * Complex.I))))) := by
  let T := primitiveHorizontalHeightSeq hq hGRH hp hne hinv
  have ht (n : ℕ) : 0 < T n :=
    zero_lt_one.trans_le
      ((le_add_of_nonneg_left (Nat.cast_nonneg n)).trans
        (primitiveHorizontalHeightSeq_ge hq hGRH hp hne hinv n))
  have hleft := integrable_completed_left_line K hp hne hinv ha haleft ha' (zero_lt_one.trans_le hx)
  have hright := integrable_completed_right_line K hne hbright hb hb' (zero_lt_one.trans_le hx)
  have h :=
    tendsto_completed_boundaryIntegral K hq hGRH hp hne hinv hab.le ha hb (by linarith only [ha'])
      hb' hx (by simpa only [mul_comm] using hleft) (by simpa only [mul_comm] using hright)
  apply h.congr
  intro n
  apply completedFiniteContourIdentity K hp hne (zero_lt_one.trans_le hx)
  · simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using
      hab
  · have hnn : -T n < T n := neg_lt_self (ht n)
    simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
      zero_sub] using hnn
  · exact closed_goodHeight_box_subset_region K hab.le ha hb
  · exact completedKernelSingularities_interior_goodHeight hq hGRH hp hne hinv n haleft hbright

end PseudoPrime.LLS.PaperStatements.MellinKernel
