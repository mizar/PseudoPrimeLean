/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedLogResidues
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.LocalResidueAssembly

/-!
# Finite shifted logarithmic contour formula

Construct the translated zero ledger with its Mellin origin and assemble the local residues
on an arbitrary ordered rectangle whose singularities are interior.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a non-principal character, the shifted L-zeros and the Mellin origin in any closed
rectangle form a finite set. Translate the compact rectangle, use compact zero finiteness,
and pull back under the injective translation. This certifies the shifted ledger. -/
theorem finite_shiftedLogSingularities {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1)
    (σ : ℝ) (z w : ℂ) :
    {s ∈ Rectangle.rectangleClosedBox z w | s = 0 ∨ χ.LFunction ((σ : ℂ) + s) = 0}.Finite := by
  have hc : IsCompact ((fun s : ℂ => (σ : ℂ) + s) '' Rectangle.rectangleClosedBox z w) :=
    (Rectangle.isCompact_rectangleClosedBox z w).image (continuous_const.add continuous_id)
  have hf := finite_dirichletLFunction_zerosOn χ hne hc
  have hi : Function.Injective (fun s : ℂ => (σ : ℂ) + s) := fun _ _ h => add_left_cancel h
  have hp := Set.Finite.preimage hi.injOn hf
  apply (hp.union (Set.finite_singleton (0 : ℂ))).subset
  intro s hs
  rcases hs.2 with hzero | hL
  · exact Or.inr hzero
  · exact Or.inl ⟨⟨s, hs.1, rfl⟩, hL⟩

/-- The finite ledger of the Mellin origin and shifted L-zeros inside a closed rectangle.
The real shift `σ` places each L-zero `ρ` at `ρ-σ`; finite zero support supplies the finset.
This indexes the finite shifted residue formula. -/
noncomputable def shiftedLogSingularitiesInRectangle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) (σ : ℝ) (z w : ℂ) : Finset ℂ :=
  (finite_shiftedLogSingularities χ hne σ z w).toFinset

/-- Membership in the shifted ledger means rectangle membership and either being the
origin or a zero of L at `σ+s`. Unfold finite-set conversion to recover these analytic
conditions for grid avoidance and local residue certificates. -/
theorem mem_shiftedLogSingularitiesInRectangle {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {hne : χ ≠ 1} {σ : ℝ} {z w s : ℂ} :
    s ∈ shiftedLogSingularitiesInRectangle χ hne σ z w ↔
      s ∈ Rectangle.rectangleClosedBox z w ∧ (s = 0 ∨ χ.LFunction ((σ : ℂ) + s) = 0) := by
  simp only [shiftedLogSingularitiesInRectangle, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- For a non-principal character and x>0, the shifted kernel is differentiable away from
the origin and shifted L-zeros. Compose the analytic logarithmic derivative with translation,
then multiply by the analytic power and divide by the nonzero square. -/
theorem differentiableAt_shiftedLogContourKernel {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {x σ : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) (hL : χ.LFunction ((σ : ℂ) + s) ≠ 0) :
    DifferentiableAt ℂ (shiftedLogContourKernel χ x σ) s := by
  have hF := (χ.differentiable_LFunction hne).analyticAt ((σ : ℂ) + s)
  have hlog : AnalyticAt ℂ (logDeriv χ.LFunction) ((σ : ℂ) + s) := hF.deriv.div hF hL
  have hc : AnalyticAt ℂ (fun u : ℂ => logDeriv χ.LFunction ((σ : ℂ) + u)) s :=
    hlog.comp (analyticAt_const.add analyticAt_id)
  have hp : AnalyticAt ℂ (fun u : ℂ => (x : ℂ) ^ u) s :=
    analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx)
  have hd := (hc.neg.mul hp).div (analyticAt_id.pow 2) (pow_ne_zero 2 hs)
  have heq :
    shiftedLogContourKernel χ x σ = fun u : ℂ =>
      -logDeriv χ.LFunction ((σ : ℂ) + u) * (x : ℂ) ^ u / u ^ 2 := by
    funext u
    simp only [shiftedLogContourKernel, logDeriv_apply, neg_div]
  rw [heq]
  exact hd.differentiableAt

/-- The residue coefficient of the shifted logarithmic kernel: its double-pole expression
at the origin, and minus the L-zero multiplicity times `x^s/s²` elsewhere. The zero term
is used on the shifted zero ledger; multiplying by `2πi` gives the local boundary integral. -/
noncomputable def shiftedLogResidueAt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x σ : ℝ)
    (s : ℂ) : ℂ :=
  if s = 0 then
    -deriv (logDeriv χ.LFunction) (σ : ℂ) - logDeriv χ.LFunction (σ : ℂ) * (Real.log x : ℂ)
  else -(dirichletLFunctionZeroMultiplicity χ ((σ : ℂ) + s) : ℂ) * (x : ℂ) ^ s / s ^ 2

/-- For a non-principal character, x>0, shift σ>=1 and an ordered rectangle whose shifted
ledger lies in its interior, the boundary integral is `2πi` times the finite residue sum.
Apply the generic grid assembly to kernel differentiability and the origin and zero square
certificates. No RH or primitivity hypothesis is needed. -/
theorem shiftedLogFiniteContourIdentity {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {x σ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im)
    (hopen :
      ∀ s ∈ shiftedLogSingularitiesInRectangle χ hne σ z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ) z w =
      ∑ s ∈ shiftedLogSingularitiesInRectangle χ hne σ z w,
        2 * Real.pi * Complex.I * shiftedLogResidueAt χ x σ s := by
  apply
    RectangleGeometry.rectangleBoundaryIntegral_eq_sum_of_local_residues
      (shiftedLogContourKernel χ x σ)
      (fun s => 2 * Real.pi * Complex.I * shiftedLogResidueAt χ x σ s)
      (shiftedLogSingularitiesInRectangle χ hne σ z w) hre him
      (fun s hs => (mem_shiftedLogSingularitiesInRectangle.mp hs).1) hopen
  · intro s hs hnot
    have hregular : ¬(s = 0 ∨ χ.LFunction ((σ : ℂ) + s) = 0) := fun h =>
      hnot (mem_shiftedLogSingularitiesInRectangle.mpr ⟨hs, h⟩)
    exact
      differentiableAt_shiftedLogContourKernel hne hx (fun h => hregular (Or.inl h))
        (fun h => hregular (Or.inr h))
  · intro s hs
    by_cases hs0 : s = 0
    · subst s
      simpa only [shiftedLogResidueAt, ↓reduceIte] using
        exists_radius_shiftedLogContourKernel_origin hne hx hσ
    · have hzero : χ.LFunction ((σ : ℂ) + s) = 0 :=
        ((mem_shiftedLogSingularitiesInRectangle.mp hs).2).resolve_left hs0
      have hshift : (σ : ℂ) + s - (σ : ℂ) = s := by ring
      have hcert := exists_radius_shiftedLogContourKernel_zero hne hx hzero (hshift ▸ hs0)
      simpa only [hshift, shiftedLogResidueAt, ite_eq_right hs0] using hcert

/-- Normalize the finite shifted contour identity by `-i/(2π)` to obtain the sum of residue
coefficients. For the same non-principal data and interior ledger, distribute over the finite
sum and cancel `i²=-1`. This form feeds the subsequent height limit. -/
theorem shiftedLogFiniteContourIdentity_normalized {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {x σ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im)
    (hopen :
      ∀ s ∈ shiftedLogSingularitiesInRectangle χ hne σ z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    (-Complex.I / (2 * (Real.pi : ℂ))) *
        RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ) z w =
      ∑ s ∈ shiftedLogSingularitiesInRectangle χ hne σ z w, shiftedLogResidueAt χ x σ s := by
  rw [shiftedLogFiniteContourIdentity hne hx hσ hre him hopen, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (-Complex.I / (2 * (Real.pi : ℂ))) * (2 * Real.pi * Complex.I) = 1 := by
    field_simp [hpi]
    norm_num only [Complex.I_sq]
  rw [← mul_assoc, hc, one_mul]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
