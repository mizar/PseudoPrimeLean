/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HeightRectangle
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLeftVerticalBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity

/-!
# Reciprocal finite-contour identities at selected heights

Apply the finite rectangle residue theorem to the corners `-A-1/2-iT_k` and `2+iT_k`.
The general GRH wrappers retain an explicit hypothesis that the singularity ledger lies
in the open rectangle. The quadratic wrappers obtain that certificate from
`primitiveHorizontalHeightSeq_singularities_mem_open`. Normalized forms cancel `2πi`.
The local centered-square residue certificate only requires a nontrivial character.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `x > 0`, a nontrivial character, and an ordinary `L`-zero away from `0,1`.
Conclusion: some centered square has reciprocal boundary integral equal to `2πi` times that
zero's designated contribution.
Content: feed the local analytic regularization and scaled-kernel equality to the shared rectangle
simple-pole theorem.
Role: this is the local reciprocal residue certificate consumed by punctured-grid bookkeeping.
-/
theorem exists_dirichletRectangleBoundaryIntegral_reciprocal_eq_two_pi_I_mul_zeroContribution
    {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        RectangleGeometry.rectangleBoundaryIntegral
            (dirichletReciprocalContourKernel x
              χ)
            (RectangleGeometry.centeredSquareLower ρ R)
            (RectangleGeometry.centeredSquareUpper ρ R) =
          2 * Real.pi * Complex.I *
            (-(dirichletLFunctionZeroMultiplicity
                      χ ρ :
                    ℂ) *
                (x : ℂ) ^ (ρ - 1) /
              (ρ * (ρ - 1))) := by
  obtain ⟨g, -, hganalytic, hgzero, heq⟩ :=
    exists_eventuallyEq_reciprocalKernel_dirichletLFunctionZeroRegularization
      x hχ hρ0 hρ1 hzero
  have hh :
    AnalyticAt ℂ
      (dirichletReciprocalZeroRegularization x ρ
        (dirichletLFunctionZeroMultiplicity χ ρ)
        g)
      ρ :=
    analyticAt_dirichletReciprocalZeroRegularization
      hx hρ0 hρ1 _ hganalytic hgzero
  obtain ⟨R, hR, hRes⟩ :=
    RectangleGeometry.exists_rectangleBoundaryIntegral_eq_two_pi_I_mul
      hh heq
  refine ⟨R, hR, ?_⟩
  simpa only [RectangleGeometry.rectangleBoundaryIntegral,
    smul_eq_mul, neg_mul] using
    (hRes.trans
      (by
        rw [dirichletReciprocalZeroRegularization_self]
        ring))

/-- Generic finite-contour identity for the GRH height-sequence corners. -/
theorem dirichletReciprocalFiniteContourIdentity_heightSeq_of_grh {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (A k : ℕ)
    (hA : 2 ≤ A)
    (hopen :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne
            (primitiveHeightSeqLowerCorner_of_grh
              hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh
              hN2 hGRH hprimitive hne hinv k),
        s ∈
          RectangleGeometry.rectangleOpenBox
            (primitiveHeightSeqLowerCorner_of_grh
              hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh
              hN2 hGRH hprimitive hne hinv k)) :
    RectangleGeometry.rectangleBoundaryIntegral
        (dirichletReciprocalContourKernel x χ)
        (primitiveHeightSeqLowerCorner_of_grh
          hN2 hGRH hprimitive hne hinv A k)
        (primitiveHeightSeqUpperCorner_of_grh
          hN2 hGRH hprimitive hne hinv k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne
            (primitiveHeightSeqLowerCorner_of_grh
              hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh
              hN2 hGRH hprimitive hne hinv k),
        2 * Real.pi * Complex.I *
          dirichletReciprocalResidueAt hne x
            s := by
  obtain ⟨_, _, _, _, hre, him⟩ :=
    primitiveHeightSeqRectangleFacts_of_grh hN2
      hGRH hprimitive hne hinv A k hA
  exact
    dirichletReciprocalFiniteContourIdentity hx
      hprimitive hne hre him hopen

/-- Normalized form of the generic reciprocal finite-contour identity. -/
theorem dirichletReciprocalFiniteContourIdentity_normalized {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hopen :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral
          (dirichletReciprocalContourKernel x χ)
          z w =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne z w,
        dirichletReciprocalResidueAt hne x
          s := by
  rw [dirichletReciprocalFiniteContourIdentity
      hx hprimitive hne hre him hopen,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]
  rw [Complex.I_sq]
  ring

/-- Normalized reciprocal identity for the Generic GRH height-sequence corners. -/
theorem dirichletReciprocalFiniteContourIdentity_heightSeq_normalized_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (A k : ℕ)
    (hA : 2 ≤ A)
    (hopen :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne
            (primitiveHeightSeqLowerCorner_of_grh
              hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh
              hN2 hGRH hprimitive hne hinv k),
        s ∈
          RectangleGeometry.rectangleOpenBox
            (primitiveHeightSeqLowerCorner_of_grh
              hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh
              hN2 hGRH hprimitive hne hinv k)) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral
          (dirichletReciprocalContourKernel x χ)
          (primitiveHeightSeqLowerCorner_of_grh
            hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner_of_grh
            hN2 hGRH hprimitive hne hinv k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne
            (primitiveHeightSeqLowerCorner_of_grh
              hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh
              hN2 hGRH hprimitive hne hinv k),
        dirichletReciprocalResidueAt hne x
          s := by
  obtain ⟨_, _, _, _, hre, him⟩ :=
    primitiveHeightSeqRectangleFacts_of_grh hN2
      hGRH hprimitive hne hinv A k hA
  exact
    dirichletReciprocalFiniteContourIdentity_normalized
      hx hprimitive hne hre him hopen

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`, `x > 0`,
`A ≥ 2`.
Conclusion: the height-sequence rectangle's boundary integral equals `2πi` times the residue sum
over its primitive singularity ledger.
Content: `DirichletLFunction.dirichletReciprocalFiniteContourIdentity` fed by the corner facts and
`hopen`
(`DirichletLFunction.primitiveHorizontalHeightSeq_singularities_mem_open`).
Role: the height-sequence specialization of the generic finite contour identity,
ready for the `k → ∞` limit assembly.
-/
theorem dirichletReciprocalFiniteContourIdentity_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (A k : ℕ) (hA : 2 ≤ A) :
    RectangleGeometry.rectangleBoundaryIntegral
        (dirichletReciprocalContourKernel x χ)
        (primitiveReciprocalLowerCorner hN2 hGRH
          hprimitive hne hinv hquad A k)
        (primitiveReciprocalUpperCorner hN2 hGRH
          hprimitive hne hinv hquad k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne
            (primitiveReciprocalLowerCorner hN2
              hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2
              hGRH hprimitive hne hinv hquad k),
        2 * Real.pi * Complex.I *
          dirichletReciprocalResidueAt hne x
            s := by
  obtain ⟨_, _, _, _, hre, him⟩ :=
    primitiveReciprocalCorners_facts hN2 hGRH
      hprimitive hne hinv hquad A k hA
  exact
    dirichletReciprocalFiniteContourIdentity hx
      hprimitive hne hre him
      (primitiveHorizontalHeightSeq_singularities_mem_open
        hN2 hGRH hprimitive hne hinv hquad A k hA)

/--
Input/assumptions: as above.
Conclusion: `(-i / 2π) · Boundary_{A,k} = ∑ r(s)` over the primitive singularity ledger.
Content: `2πi · (-i / 2π) = 1`, so the height-sequence identity's `2πi` factor cancels termwise.
Role: the normalized contour identity, matching the boxed target `(-i/2π) Boundary = ∑ r(s)` used
by the final `k → ∞`/`A → ∞` assembly (so the right edge lines up directly with
`DirichletLFunction.characterReciprocalWeightedSum_eq_integral`'s `(2π)⁻¹ •` normalization).
-/
theorem dirichletReciprocalFiniteContourIdentity_heightSeq_normalized {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (A k : ℕ) (hA : 2 ≤ A) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral
          (dirichletReciprocalContourKernel x χ)
          (primitiveReciprocalLowerCorner hN2
            hGRH hprimitive hne hinv hquad A k)
          (primitiveReciprocalUpperCorner hN2
            hGRH hprimitive hne hinv hquad k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne
            (primitiveReciprocalLowerCorner hN2
              hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2
              hGRH hprimitive hne hinv hquad k),
        dirichletReciprocalResidueAt hne x
          s := by
  rw [dirichletReciprocalFiniteContourIdentity_heightSeq
      hN2 hGRH hprimitive hne hinv hquad hx A k hA,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero,
      or_self, not_false_eq_true]
  have hcoeff : (-Complex.I / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [div_mul_eq_mul_div, mul_comm (2 * (Real.pi : ℂ)) Complex.I, ← mul_assoc,
      show (-Complex.I) * Complex.I = 1 from by
        rw [neg_mul, Complex.I_mul_I]; ring,
      one_mul, div_self h2pi]
  calc
    (-Complex.I / (2 * (Real.pi : ℂ))) *
          (2 * Real.pi * Complex.I *
            dirichletReciprocalResidueAt hne x
              s) =
        ((-Complex.I / (2 * (Real.pi : ℂ))) * (2 * Real.pi * Complex.I)) *
          dirichletReciprocalResidueAt hne x
            s :=
      by ring
    _ = dirichletReciprocalResidueAt hne x s :=
      by rw [hcoeff, one_mul]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
