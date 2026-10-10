/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HeightRectangle
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLeftVerticalBound
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity

/-!
# Reciprocal finite-contour identities at selected heights

Apply the finite rectangle residue theorem to the corners `-A-1/2-iT_k` and `2+iT_k`.
The general GRH wrappers retain an explicit hypothesis that the singularity ledger lies
in the open rectangle. The quadratic wrappers obtain that certificate from
`primitiveHeightSeq_singularities_mem_open`. Normalized forms cancel `2πi`.
The local centered-square residue certificate only requires a nontrivial character.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Normalized form of the generic reciprocal finite-contour identity. -/
theorem dirichletReciprocalFiniteContourIdentity_normalized {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hopen :
      ∀ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral (dirichletReciprocalContourKernel x χ) z w =
      ∑ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
        dirichletReciprocalResidueAt hne x s := by
  rw [dirichletReciprocalFiniteContourIdentity hx hprimitive hne hre him hopen, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num only) hπ
  calc
    -Complex.I / (2 * ↑Real.pi) *
          (2 * ↑Real.pi * Complex.I * dirichletReciprocalResidueAt hne x s) =
        (2 * ↑Real.pi) * (-Complex.I * Complex.I * dirichletReciprocalResidueAt hne x s) /
          (2 * ↑Real.pi) :=
      by
      rw [div_mul_eq_mul_div]
      congr 1
      ring
    _ = -Complex.I * Complex.I * dirichletReciprocalResidueAt hne x s :=
      mul_div_cancel_left₀ _ hprod
    _ = dirichletReciprocalResidueAt hne x s := by
      rw [neg_mul, Complex.I_mul_I]
      ring

/-- Under the primitive-character GRH hypotheses, `x > 0`, `A ≥ 2`, and explicit open-rectangle
membership of every listed singularity, the boundary integral multiplied by `-i/(2π)` equals
the finite reciprocal residue sum. The selected corner facts reduce this to the normalized
rectangle identity, supplying the normalization used by the subsequent height-limit argument. -/
theorem dirichletReciprocalFiniteContourIdentity_heightSeq_normalized {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (A k : ℕ)
    (hA : 2 ≤ A)
    (hopen :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle χ hne
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k),
        s ∈
          RectangleGeometry.rectangleOpenBox
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k)) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral (dirichletReciprocalContourKernel x χ)
          (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle χ hne
            (primitiveHeightSeqLowerCorner hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner hN2 hGRH hprimitive hne hinv k),
        dirichletReciprocalResidueAt hne x s := by
  obtain ⟨_, _, _, _, hre, him⟩ :=
    primitiveHeightSeqRectangleFacts hN2 hGRH hprimitive hne hinv A k hA
  exact dirichletReciprocalFiniteContourIdentity_normalized hx hprimitive hne hre him hopen

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
