/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.GridCutConstruction

/-!
# Generic singular-cell shrink helpers

This file generalizes the "singular cell → centered square" shrink machinery used by an
explicit-formula contour over an arbitrary finite singularity set `S : Finset ℂ`.

The end result, `RectangleGeometry.SingularCellAssignment.parent_boundaryIntegral_eq_of_shrink`,
lifts a local
residue certificate (valid on a small centered square around an assigned singularity) up to the
*entire singular parent cell's* boundary integral — the missing bridge between the analytic assembly
`RectangleGeometry.rectangleBoundaryIntegral_eq_sum_res` (which wants each singular cell's full
boundary integral)
and local residue theorems (which are only about small
centered squares).

Unlike a kernel-specific regular set, this file works with plain
`Disjoint (PseudoPrime.AnalyticNumberTheory.Rectangle.rectangleClosedBox ·) (S : Set ℂ)` facts,
which combine with differentiability off `S` within the parent cell to make each surrounding
cell's boundary integral vanish.
-/

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/--
A subrectangle of a singular cell is disjoint from `S` when it excludes the cell's assigned
singularity: every point of `S` inside the parent cell equals the assigned point, so excluding
that one point from the subrectangle excludes all of `S`.
-/
theorem SingularCellAssignment.subcell_disjoint {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : SingularCellAssignment S cells)
    {parent child : ℂ × ℂ}
    (hparent :
      parent ∈ finiteSingularCells S cells)
    (hchildSubset :
      Rectangle.rectangleClosedBox child.1 child.2 ⊆
        Rectangle.rectangleClosedBox parent.1 parent.2)
    (hexclude :
      assignment.pointOfCell parent ∉
        Rectangle.rectangleClosedBox child.1 child.2) :
    Disjoint (Rectangle.rectangleClosedBox child.1 child.2)
      (S : Set ℂ) := by
  apply Set.disjoint_left.mpr
  intro s hschild hsS
  have heq := assignment.point_unique parent hparent s hsS (hchildSubset hschild)
  exact hexclude (heq ▸ hschild)

/--
Every noncentral cell of a `3 × 3` subdivision of a singular parent cell (split around a square
`[a, b]` containing the assigned singularity) is disjoint from `S`: it excludes the assigned point
by `RectangleGeometry.not_mem_noncentral_threeByThreeGridCell`, and `subcell_disjoint` upgrades
that exclusion to
full disjointness from `S`.
-/
theorem SingularCellAssignment.threeByThree_noncentral_disjoint {S : Finset ℂ}
    {cells : Finset (ℂ × ℂ)}
    (assignment : SingularCellAssignment S cells)
    {parent : ℂ × ℂ}
    (hparent :
      parent ∈ finiteSingularCells S cells)
    {a b : ℂ} (hzare : parent.1.re < a.re) (habre : a.re < b.re) (hbwre : b.re < parent.2.re)
    (hzaim : parent.1.im < a.im) (habim : a.im < b.im) (hbwim : b.im < parent.2.im)
    (hpoint :
      assignment.pointOfCell parent ∈
        rectangleOpenBox a b)
    {child : ℂ × ℂ}
    (hchild :
      child ∈
        rectangleGridCells parent.1 parent.2
          [a.re, b.re] [a.im, b.im])
    (hne : child ≠ (a, b)) :
    Disjoint (Rectangle.rectangleClosedBox child.1 child.2)
      (S : Set ℂ) := by
  have hxcuts : ∀ u ∈ [a.re, b.re], u ∈ Set.uIcc parent.1.re parent.2.re := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact Set.mem_uIcc_of_le hzare.le (habre.trans hbwre).le
    · exact Set.mem_uIcc_of_le (hzare.trans habre).le hbwre.le
  have hycuts : ∀ v ∈ [a.im, b.im], v ∈ Set.uIcc parent.1.im parent.2.im := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact Set.mem_uIcc_of_le hzaim.le (habim.trans hbwim).le
    · exact Set.mem_uIcc_of_le (hzaim.trans habim).le hbwim.le
  have hchildSubset :=
    rectangleGridCells_closedBox_subset hxcuts
      hycuts child hchild
  apply assignment.subcell_disjoint hparent hchildSubset
  exact
    not_mem_noncentral_threeByThreeGridCell hzare
      habre hbwre hzaim habim hbwim hpoint hchild hne

/-- The noncentral-disjointness theorem in the finite-set form used by contour contraction. -/
theorem SingularCellAssignment.threeByThree_surrounding_disjoint {S : Finset ℂ}
    {cells : Finset (ℂ × ℂ)}
    (assignment : SingularCellAssignment S cells)
    {parent : ℂ × ℂ}
    (hparent :
      parent ∈ finiteSingularCells S cells)
    {a b : ℂ} (hzare : parent.1.re < a.re) (habre : a.re < b.re) (hbwre : b.re < parent.2.re)
    (hzaim : parent.1.im < a.im) (habim : a.im < b.im) (hbwim : b.im < parent.2.im)
    (hpoint :
      assignment.pointOfCell parent ∈
        rectangleOpenBox a b) :
    ∀
      child ∈
        (rectangleGridCells parent.1 parent.2
            [a.re, b.re] [a.im, b.im]).toFinset,
      child ≠ (a, b) →
        Disjoint (Rectangle.rectangleClosedBox child.1 child.2)
          (S : Set ℂ) := by
  intro child hchild hne
  exact
    assignment.threeByThree_noncentral_disjoint hparent hzare habre hbwre hzaim habim hbwim hpoint
      (by simpa only [List.mem_toFinset] using hchild) hne

/-- Interior separation places each assigned singularity in its cell's open rectangle. -/
theorem GridInteriorSeparation.pointOfCell_mem_open {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : GridInteriorSeparation S cells)
    {cell : ℂ × ℂ}
    (hcell :
      cell ∈ finiteSingularCells S cells) :
    interior.toAssignment.pointOfCell cell ∈
      rectangleOpenBox cell.1 cell.2 := by
  apply interior.point_mem_open
  · exact interior.toAssignment.point_mem_ledger cell hcell
  · exact (mem_singularCells_iff.mp hcell).1
  · exact interior.toAssignment.point_mem_cell cell hcell

/-- Every assigned singularity has a positive closed ball contained in its open cell. -/
theorem GridInteriorSeparation.exists_closedBall_pointOfCell_subset_open {S : Finset ℂ}
    {cells : Finset (ℂ × ℂ)}
    (interior : GridInteriorSeparation S cells)
    {cell : ℂ × ℂ}
    (hcell :
      cell ∈ finiteSingularCells S cells) :
    ∃ ε : ℝ,
      0 < ε ∧
        Metric.closedBall (interior.toAssignment.pointOfCell cell) ε ⊆
          rectangleOpenBox cell.1 cell.2 :=
  exists_closedBall_subset_rectangleOpenBox
    (interior.pointOfCell_mem_open hcell)

/-- All assigned singularities admit one common positive radius contained in their open cells. -/
theorem GridInteriorSeparation.exists_common_cell_radius {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : GridInteriorSeparation S cells) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ cell ∈ finiteSingularCells S cells,
          Metric.closedBall (interior.toAssignment.pointOfCell cell) ε ⊆
            rectangleOpenBox cell.1 cell.2 := by
  apply Finset.exists_common_closedBall_subset
  intro cell hcell
  exact interior.exists_closedBall_pointOfCell_subset_open hcell

/--
**The shrink theorem**: a singular parent cell's *entire* boundary integral equals the boundary
integral of any ordered rectangle strictly inside it that still contains the assigned singularity
in its interior — given only that `f` is differentiable off `S` *within the parent cell* (a local
hypothesis: `f` need not be differentiable anywhere outside the parent, matching the finite residue
theorem's localized
`hdiff`) and the grid-subdivision integrability of `f` on the induced `3 × 3` grid (left to the
caller, exactly as the finite residue theorem leaves the outer grid-subdivision decomposition to
the caller). Combined
with a local residue certificate on that centered square, this identifies the parent cell's
boundary integral with `2πi · res`.
-/
theorem SingularCellAssignment.parent_boundaryIntegral_eq_of_shrink {S : Finset ℂ}
    {cells : Finset (ℂ × ℂ)}
    (assignment : SingularCellAssignment S cells)
    (f : ℂ → ℂ) {parent : ℂ × ℂ}
    (hparent :
      parent ∈ finiteSingularCells S cells)
    {a b : ℂ} (hzare : parent.1.re < a.re) (habre : a.re < b.re) (hbwre : b.re < parent.2.re)
    (hzaim : parent.1.im < a.im) (habim : a.im < b.im) (hbwim : b.im < parent.2.im)
    (hpoint :
      assignment.pointOfCell parent ∈
        rectangleOpenBox a b)
    (hdiff :
      ∀ x ∈ Rectangle.rectangleClosedBox parent.1 parent.2,
        x ∉ S → DifferentiableAt ℂ f x)
    (hgrid :
      RectangleGridSubdivisionIntegrable f
        parent.1 parent.2 [a.re, b.re] [a.im, b.im]) :
    rectangleBoundaryIntegral f parent.1
        parent.2 =
      rectangleBoundaryIntegral f a b := by
  have hxcuts : ∀ u ∈ [a.re, b.re], u ∈ Set.uIcc parent.1.re parent.2.re := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact Set.mem_uIcc_of_le hzare.le (habre.trans hbwre).le
    · exact Set.mem_uIcc_of_le (hzare.trans habre).le hbwre.le
  have hycuts : ∀ v ∈ [a.im, b.im], v ∈ Set.uIcc parent.1.im parent.2.im := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact Set.mem_uIcc_of_le hzaim.le (habim.trans hbwim).le
    · exact Set.mem_uIcc_of_le (hzaim.trans habim).le hbwim.le
  apply
    rectangleBoundaryIntegral_eq_innerRectangle f
      parent.1 parent.2 a b hgrid
      (threeByThreeGrid_nodup hzare habre hbwre
        hzaim habim hbwim)
  intro cell hcell hne
  have hdisjoint :=
    assignment.threeByThree_surrounding_disjoint hparent hzare habre hbwre hzaim habim hbwim hpoint
      cell hcell hne
  have hcellSubset :=
    rectangleGridCells_closedBox_subset hxcuts
      hycuts cell (by simpa only [List.mem_toFinset] using hcell)
  apply
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro x hx
  apply (hdiff x (hcellSubset hx) ?_).differentiableWithinAt
  intro hxS
  exact Set.disjoint_left.mp hdisjoint hx hxS

/--
Coordinate-line integrability of `f` on any two lists of real/imaginary coordinates confined to a
singular parent cell and avoiding the cell's assigned point — the ingredient
`parent_boundaryIntegral_eq_of_shrink`'s `hgrid` hypothesis needs, via
`RectangleGeometry.RectangleGridCoordinateIntegrable.gridSubdivision`. A segment
between two `xcoordinates`/`ycoordinates` at a third coordinate is itself a degenerate rectangle
inside the parent cell, so `subcell_disjoint` applies to it exactly as to any other subcell. As in
`parent_boundaryIntegral_eq_of_shrink`, `hdiff` is localized to the parent cell rather than global.
-/
theorem SingularCellAssignment.kernelCoordinateIntegrable {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : SingularCellAssignment S cells)
    (f : ℂ → ℂ) {parent : ℂ × ℂ}
    (hparent :
      parent ∈ finiteSingularCells S cells)
    (hdiff :
      ∀ x ∈ Rectangle.rectangleClosedBox parent.1 parent.2,
        x ∉ S → DifferentiableAt ℂ f x)
    (xcoordinates ycoordinates : List ℝ)
    (hxmem : ∀ c ∈ xcoordinates, c ∈ Set.uIcc parent.1.re parent.2.re)
    (hymem : ∀ c ∈ ycoordinates, c ∈ Set.uIcc parent.1.im parent.2.im)
    (hxavoid : ∀ c ∈ xcoordinates, (assignment.pointOfCell parent).re ≠ c)
    (hyavoid : ∀ c ∈ ycoordinates, (assignment.pointOfCell parent).im ≠ c) :
    RectangleGridCoordinateIntegrable f
      xcoordinates ycoordinates := by
  have hre (u v : ℝ) : ((u : ℂ) + v * Complex.I).re = u := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have him (u v : ℝ) : ((u : ℂ) + v * Complex.I).im = v := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  constructor
  · intro c hc a ha b hb
    apply
      intervalIntegrable_horizontal_of_continuousAt
    intro t ht
    have hchildSubset :
      Rectangle.rectangleClosedBox ((a : ℂ) + c * Complex.I)
          ((b : ℂ) + c * Complex.I) ⊆
        Rectangle.rectangleClosedBox parent.1 parent.2 := by
      intro s hs
      have hs1 : s.re ∈ Set.uIcc ((a : ℂ) + c * Complex.I).re ((b : ℂ) + c * Complex.I).re := hs.1
      have hs2 : s.im ∈ Set.uIcc ((a : ℂ) + c * Complex.I).im ((b : ℂ) + c * Complex.I).im := hs.2
      rw [hre a c, hre b c] at hs1
      rw [him a c, him b c] at hs2
      exact
        ⟨Set.uIcc_subset_uIcc (hxmem a ha) (hxmem b hb) hs1,
          Set.uIcc_subset_uIcc (hymem c hc) (hymem c hc) hs2⟩
    have hexclude :
      assignment.pointOfCell parent ∉
        Rectangle.rectangleClosedBox ((a : ℂ) + c * Complex.I)
          ((b : ℂ) + c * Complex.I) := by
      intro hmem
      have hmem2 :
        (assignment.pointOfCell parent).im ∈
          Set.uIcc ((a : ℂ) + c * Complex.I).im ((b : ℂ) + c * Complex.I).im :=
        hmem.2
      rw [him a c, him b c, Set.uIcc_self] at hmem2
      exact hyavoid c hc (Set.mem_singleton_iff.mp hmem2)
    have hdisjoint :=
      assignment.subcell_disjoint (child := ((a : ℂ) + c * Complex.I, (b : ℂ) + c * Complex.I))
        hparent hchildSubset hexclude
    have hseg :
      ((t : ℂ) + c * Complex.I) ∈
        Rectangle.rectangleClosedBox ((a : ℂ) + c * Complex.I)
          ((b : ℂ) + c * Complex.I) := by
      rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm,
        hre a c, hre b c, him a c, him b c, hre t c, him t c]
      exact ⟨ht, Set.mem_uIcc_of_le le_rfl le_rfl⟩
    have hdiffAt : DifferentiableAt ℂ f ((t : ℂ) + c * Complex.I) := by
      apply hdiff _ (hchildSubset hseg)
      intro hxS
      exact Set.disjoint_left.mp hdisjoint hseg hxS
    exact hdiffAt.continuousAt
  · intro c hc a ha b hb
    apply
      intervalIntegrable_vertical_of_continuousAt
    intro t ht
    have hchildSubset :
      Rectangle.rectangleClosedBox ((c : ℂ) + a * Complex.I)
          ((c : ℂ) + b * Complex.I) ⊆
        Rectangle.rectangleClosedBox parent.1 parent.2 := by
      intro s hs
      have hs1 : s.re ∈ Set.uIcc ((c : ℂ) + a * Complex.I).re ((c : ℂ) + b * Complex.I).re := hs.1
      have hs2 : s.im ∈ Set.uIcc ((c : ℂ) + a * Complex.I).im ((c : ℂ) + b * Complex.I).im := hs.2
      rw [hre c a, hre c b] at hs1
      rw [him c a, him c b] at hs2
      exact
        ⟨Set.uIcc_subset_uIcc (hxmem c hc) (hxmem c hc) hs1,
          Set.uIcc_subset_uIcc (hymem a ha) (hymem b hb) hs2⟩
    have hexclude :
      assignment.pointOfCell parent ∉
        Rectangle.rectangleClosedBox ((c : ℂ) + a * Complex.I)
          ((c : ℂ) + b * Complex.I) := by
      intro hmem
      have hmem1 :
        (assignment.pointOfCell parent).re ∈
          Set.uIcc ((c : ℂ) + a * Complex.I).re ((c : ℂ) + b * Complex.I).re :=
        hmem.1
      rw [hre c a, hre c b, Set.uIcc_self] at hmem1
      exact hxavoid c hc (Set.mem_singleton_iff.mp hmem1)
    have hdisjoint :=
      assignment.subcell_disjoint (child := ((c : ℂ) + a * Complex.I, (c : ℂ) + b * Complex.I))
        hparent hchildSubset hexclude
    have hseg :
      ((c : ℂ) + t * Complex.I) ∈
        Rectangle.rectangleClosedBox ((c : ℂ) + a * Complex.I)
          ((c : ℂ) + b * Complex.I) := by
      rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm,
        hre c a, hre c b, him c a, him c b, hre c t, him c t]
      exact ⟨Set.mem_uIcc_of_le le_rfl le_rfl, ht⟩
    have hdiffAt : DifferentiableAt ℂ f ((c : ℂ) + t * Complex.I) := by
      apply hdiff _ (hchildSubset hseg)
      intro hxS
      exact Set.disjoint_left.mp hdisjoint hseg hxS
    exact hdiffAt.continuousAt

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry
