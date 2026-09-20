/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.ContourRegularity

/-!
# Contour regularity for Dirichlet `L`-functions

The regular set excludes L-function zeros and the exceptional points `0` and `1`.
The finite rectangle ledger and segment-avoidance theorems require no application-specific
hypothesis or kernel.
The excluded set is a sufficient exceptional set, not a claim that both points are poles.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a complex Dirichlet character.
Conclusion: the locus where a reciprocal/log Mellin-type contour kernel built from `LFunction χ`
has no Mellin or `L`-zero singularity.
Content: remove the two Mellin points and the zero set of the (uncompleted) `L`-function.
Role: regular rectangles contained here admit Cauchy--Goursat boundary identities immediately.
-/
def dirichletLFunctionContourRegularSet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Set ℂ :=
  ({0}ᶜ : Set ℂ) ∩ ({1}ᶜ : Set ℂ) ∩ (DirichletCharacter.LFunction χ) ⁻¹' ({0}ᶜ : Set ℂ)

/--
Definition: the finite singularity ledger for a reciprocal/log Mellin-type contour kernel pair
built from `LFunction χ`, inside one rectangle.
Input: a nontrivial character and rectangle corners.
Output: all `LFunction χ`-zeros in the rectangle together with whichever Mellin points `0, 1` lie
inside it.
Role: normalizes the overlap at `s = 0` in an even-character branch and indexes a punctured grid.
-/
noncomputable def dirichletLFunctionSingularitiesInRectangle {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) : Finset ℂ := by
  classical
    exact
    dirichletLFunctionZerosInRectangle χ hχ z w ∪
      (if (0 : ℂ) ∈ dirichletCompletedLFunctionRectangleBox z w then {0} else ∅) ∪
      (if (1 : ℂ) ∈ dirichletCompletedLFunctionRectangleBox z w then {1} else ∅)

/--
Input/assumptions: a point and the singularity ledger of a rectangle.
Conclusion: membership means rectangle membership and being either Mellin point or an `L`-zero.
Content: unfold the zero ledger and the two conditional singleton entries.
Role: converts finite-grid avoidance back into the analytic regularity conditions for both kernels.
-/
theorem mem_dirichletLFunctionSingularitiesInRectangle_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {z w s : ℂ} :
    s ∈ dirichletLFunctionSingularitiesInRectangle χ hχ z w ↔
      s ∈ dirichletCompletedLFunctionRectangleBox z w ∧
        (s = 0 ∨ s = 1 ∨ DirichletCharacter.LFunction χ s = 0) := by
  rw [dirichletLFunctionSingularitiesInRectangle, Finset.mem_union, Finset.mem_union]
  rw [DirichletLFunction.mem_dirichletLFunctionZerosInRectangle_iff]
  by_cases hzero : (0 : ℂ) ∈ dirichletCompletedLFunctionRectangleBox z w <;>
    by_cases hone : (1 : ℂ) ∈ dirichletCompletedLFunctionRectangleBox z w <;>
    simp only [hzero, ↓reduceIte, Finset.mem_singleton, hone] <;>
    aesop

/--
Input/assumptions: a point of the outer rectangle not listed in its singularity ledger.
Conclusion: the point is regular for a reciprocal/log Mellin-type contour kernel pair built from
`LFunction χ`.
Content: exclusion from the ledger rules out both Mellin points and all zeros of the (uncompleted)
Dirichlet `L`-function.
Role: the analytic bridge from grid-cell avoidance to Cauchy--Goursat regular cells.
-/
theorem mem_dirichletLFunctionContourRegularSet_of_not_mem_singularities {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {z w s : ℂ}
    (hrect : s ∈ dirichletCompletedLFunctionRectangleBox z w)
    (hnot : s ∉ dirichletLFunctionSingularitiesInRectangle χ hχ z w) :
    s ∈ dirichletLFunctionContourRegularSet χ := by
  have hmem :
    ∀ hu : s = 0 ∨ s = 1 ∨ DirichletCharacter.LFunction χ s = 0,
      s ∈ dirichletLFunctionSingularitiesInRectangle χ hχ z w := by
    intro hu
    exact mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr ⟨hrect, hu⟩
  have hs0 : s ≠ 0 := by
    intro hs
    exact hnot (hmem (Or.inl hs))
  have hs1 : s ≠ 1 := by
    intro hs
    exact hnot (hmem (Or.inr (Or.inl hs)))
  have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro hs
    exact hnot (hmem (Or.inr (Or.inr hs)))
  simpa only [dirichletLFunctionContourRegularSet, Set.preimage_compl, Set.mem_inter_iff,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage] using ⟨⟨hs0, hs1⟩, hL⟩

/--
Input/assumptions: a horizontal segment in the outer rectangle avoids every ledger imaginary
coordinate.
Conclusion: every point of the segment is regular for a reciprocal/log Mellin-type contour kernel
pair built from `LFunction χ`.
Content: recover outer-rectangle membership, then use the ledger membership API to exclude all
Mellin and `L`-zero singularities.
Role: supplies horizontal grid-edge regularity before interval integrability is assembled.
-/
theorem horizontal_segment_subset_dirichletLFunctionContourRegularSet {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {z w : ℂ} {c a b : ℝ} (ha : a ∈ Set.uIcc z.re w.re)
    (hb : b ∈ Set.uIcc z.re w.re) (hc : c ∈ Set.uIcc z.im w.im)
    (havoid : ∀ s ∈ dirichletLFunctionSingularitiesInRectangle χ hχ z w, s.im ≠ c) :
    ∀ t ∈ Set.uIcc a b, t + c * Complex.I ∈ dirichletLFunctionContourRegularSet χ := by
  intro t ht
  have hrect : (t : ℂ) + c * Complex.I ∈ dirichletCompletedLFunctionRectangleBox z w := by
    exact
      ⟨by
        simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using Set.uIcc_subset_uIcc ha hb ht,
        by
        simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
          zero_add] using hc⟩
  exact
    mem_dirichletLFunctionContourRegularSet_of_not_mem_singularities hrect
      (by
        exact
          RectangleGeometry.horizontal_segment_subset_compl_of_im_avoid (S :=
            (dirichletLFunctionSingularitiesInRectangle χ hχ z w : Set ℂ))
            (fun s hs => havoid s (by simpa only [Finset.mem_coe] using hs)) t ht)

/--
Input/assumptions: a vertical segment in the outer rectangle avoids every ledger real coordinate.
Conclusion: every point of the segment is regular for a reciprocal/log Mellin-type contour kernel
pair built from `LFunction χ`.
Content: the vertical counterpart of horizontal ledger avoidance.
Role: supplies vertical grid-edge regularity before interval integrability is assembled.
-/
theorem vertical_segment_subset_dirichletLFunctionContourRegularSet {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {z w : ℂ} {c a b : ℝ} (hc : c ∈ Set.uIcc z.re w.re)
    (ha : a ∈ Set.uIcc z.im w.im) (hb : b ∈ Set.uIcc z.im w.im)
    (havoid : ∀ s ∈ dirichletLFunctionSingularitiesInRectangle χ hχ z w, s.re ≠ c) :
    ∀ t ∈ Set.uIcc a b, c + t * Complex.I ∈ dirichletLFunctionContourRegularSet χ := by
  intro t ht
  have hrect : (c : ℂ) + t * Complex.I ∈ dirichletCompletedLFunctionRectangleBox z w := by
    exact
      ⟨by
        simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using hc,
        by
        simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
          zero_add] using Set.uIcc_subset_uIcc ha hb ht⟩
  exact
    mem_dirichletLFunctionContourRegularSet_of_not_mem_singularities hrect
      (by
        exact
          RectangleGeometry.vertical_segment_subset_compl_of_re_avoid (S :=
            (dirichletLFunctionSingularitiesInRectangle χ hχ z w : Set ℂ))
            (fun s hs => havoid s (by simpa only [Finset.mem_coe] using hs)) t ht)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
