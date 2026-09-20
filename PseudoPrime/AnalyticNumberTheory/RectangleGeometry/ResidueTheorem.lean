/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary

/-!
# A generic finite punctured-rectangle residue theorem

This file generalizes the finite singular-cell grid machinery used by a Riemann explicit-formula
contour to an arbitrary finite singularity set `S : Finset ℂ`.

The development has two independent layers:

* **Geometry**: `PseudoPrime.AnalyticNumberTheory.RectangleGeometry.CellContainsSingularity`,
  `RectangleGeometry.finiteRegularCells`/`RectangleGeometry.finiteSingularCells`, and
`RectangleGeometry.SingularCellAssignment` — a finite bijection
  between `S` and the "singular" grid cells that each catalogue exactly one point of `S`. None of
  this mentions an analytic function.
* **Analytic assembly**: `RectangleGeometry.rectangleBoundaryIntegral_eq_sum_res` — given such an
  assignment, a kernel `f` differentiable off `S`, a residue function `res`, and a grid-subdivision
  decomposition of the outer rectangle into `cells`, the outer boundary integral is `Σ s ∈ S,
  res s` (with the `2πi` factor folded into `res` by the caller, matching how the existing
  primitive local-residue theorems are already stated).

Grid *construction* (choosing cuts, proving `Nodup`, proving
`RectangleGeometry.RectangleGridSubdivisionIntegrable`)
is deliberately left to the caller via the existing generic
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_gridSubdivision` /
`RectangleGeometry.rectangleGridSubdivision_eq_sum_toFinset`; the assembly theorem
only consumes the resulting cell-sum decomposition as a hypothesis.
-/

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- A cell contains a singularity from the finite set `S`. -/
def CellContainsSingularity (S : Finset ℂ) (cell : ℂ × ℂ) : Prop :=
  ∃ s ∈ S, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2

/-- The cells of a finite cell ledger avoiding every singularity of `S`. -/
noncomputable def finiteRegularCells (S : Finset ℂ) (cells : Finset (ℂ × ℂ)) : Finset (ℂ × ℂ) := by
  classical exact cells.filter fun cell ↦ ¬CellContainsSingularity S cell

/-- The cells of a finite cell ledger containing at least one singularity of `S`. -/
noncomputable def finiteSingularCells (S : Finset ℂ) (cells : Finset (ℂ × ℂ)) : Finset (ℂ × ℂ) := by
  classical exact cells.filter fun cell ↦ CellContainsSingularity S cell

/-- Membership in the regular-cell filter has its expected specification. -/
theorem mem_regularCells_iff {S : Finset ℂ} {cells : Finset (ℂ × ℂ)} {cell : ℂ × ℂ} :
    cell ∈ finiteRegularCells S cells ↔ cell ∈ cells ∧ ¬CellContainsSingularity S cell := by
  classical simp only [finiteRegularCells, Finset.mem_filter]

/-- Membership in the singular-cell filter has its expected specification. -/
theorem mem_singularCells_iff {S : Finset ℂ} {cells : Finset (ℂ × ℂ)} {cell : ℂ × ℂ} :
    cell ∈ finiteSingularCells S cells ↔ cell ∈ cells ∧ CellContainsSingularity S cell := by
  classical simp only [finiteSingularCells, Finset.mem_filter]

/-- The regular and singular filters partition any finite cell sum. -/
theorem sum_finiteRegularCells_add_sum_finiteSingularCells {M : Type*} [AddCommMonoid M]
    (S : Finset ℂ) (cells : Finset (ℂ × ℂ)) (value : ℂ × ℂ → M) :
    (∑ cell ∈ finiteRegularCells S cells, value cell) +
        ∑ cell ∈ finiteSingularCells S cells, value cell =
      ∑ cell ∈ cells, value cell := by
  classical
  unfold finiteRegularCells finiteSingularCells
  rw [add_comm, Finset.sum_filter_add_sum_filter_not]

/--
A finite bijective assignment of exactly one catalogued singularity from `S` to every singular
grid cell. `pointOfCell` selects the point assigned to a cell; the first three invariants state
that this is the unique point of `S` inside that cell, `distinct_points` prevents two singular
cells from sharing an assigned point, and `point_covered` ensures every point of `S` is assigned
to some cell.
-/
structure SingularCellAssignment (S : Finset ℂ) (cells : Finset (ℂ × ℂ)) where
  pointOfCell : ℂ × ℂ → ℂ
  point_mem_ledger : ∀ cell ∈ finiteSingularCells S cells, pointOfCell cell ∈ S
  point_mem_cell :
    ∀ cell ∈ finiteSingularCells S cells,
      pointOfCell cell ∈ Rectangle.rectangleClosedBox cell.1 cell.2
  point_unique :
    ∀ cell ∈ finiteSingularCells S cells,
      ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s = pointOfCell cell
  distinct_points :
    ∀ cell ∈ finiteSingularCells S cells,
      ∀ other ∈ finiteSingularCells S cells, pointOfCell cell = pointOfCell other → cell = other
  point_covered : ∀ s ∈ S, ∃ cell ∈ finiteSingularCells S cells, pointOfCell cell = s

/--
Geometric separation conditions making grid cells and singularities correspond bijectively.
`cell_point_unique` says one cell contains at most one point of `S`; `point_cell_unique` says one
point of `S` belongs to at most one listed cell (excluding placement on shared grid edges);
`point_covered` places every point of `S` in a listed cell.
-/
structure GridSingularitySeparation (S : Finset ℂ) (cells : Finset (ℂ × ℂ)) where
  cell_point_unique :
    ∀ cell ∈ cells,
      ∀ s ∈ S,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          ∀ t ∈ S, t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s = t
  point_cell_unique :
    ∀ s ∈ S,
      ∀ cell ∈ cells,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          ∀ other ∈ cells, s ∈ Rectangle.rectangleClosedBox other.1 other.2 → cell = other
  point_covered : ∀ s ∈ S, ∃ cell ∈ cells, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2

/--
Interior geometric conditions sufficient for grid/singularity separation: each cell contains at
most one point of `S`, every such point lies in the open (not just closed) rectangle of its cell,
distinct listed open rectangles are disjoint, and every point of `S` is covered.
-/
structure GridInteriorSeparation (S : Finset ℂ) (cells : Finset (ℂ × ℂ)) where
  cell_point_unique :
    ∀ cell ∈ cells,
      ∀ s ∈ S,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          ∀ t ∈ S, t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s = t
  point_mem_open :
    ∀ s ∈ S,
      ∀ cell ∈ cells,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s ∈ rectangleOpenBox cell.1 cell.2
  open_disjoint :
    ∀ cell ∈ cells,
      ∀ other ∈ cells,
        cell ≠ other → Disjoint (rectangleOpenBox cell.1 cell.2) (rectangleOpenBox other.1 other.2)
  point_covered : ∀ s ∈ S, ∃ cell ∈ cells, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2

/-- Interior separation conditions imply the abstract grid/singularity separation certificate. -/
theorem GridInteriorSeparation.toSeparation {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : GridInteriorSeparation S cells) : GridSingularitySeparation S cells := by
  refine ⟨interior.cell_point_unique, ?_, interior.point_covered⟩
  intro s hs cell hcell hscell other hother hsother
  by_contra hne
  exact
    Set.disjoint_left.mp (interior.open_disjoint cell hcell other hother hne)
      (interior.point_mem_open s hs cell hcell hscell)
      (interior.point_mem_open s hs other hother hsother)

/-- Geometric cell/singularity separation induces the singular-cell assignment ledger. -/
noncomputable def GridSingularitySeparation.toAssignment {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (separation : GridSingularitySeparation S cells) : SingularCellAssignment S cells := by
  classical
  let pointOfCell : ℂ × ℂ → ℂ := fun cell ↦
    Classical.epsilon fun s ↦ s ∈ S ∧ s ∈ Rectangle.rectangleClosedBox cell.1 cell.2
  have point_spec (cell : ℂ × ℂ) (hcell : CellContainsSingularity S cell) :
    pointOfCell cell ∈ S ∧ pointOfCell cell ∈ Rectangle.rectangleClosedBox cell.1 cell.2 :=
    Classical.epsilon_spec hcell
  refine ⟨pointOfCell, ?_, ?_, ?_, ?_, ?_⟩
  · intro cell hcell
    exact (point_spec cell (mem_singularCells_iff.mp hcell).2).1
  · intro cell hcell
    exact (point_spec cell (mem_singularCells_iff.mp hcell).2).2
  · intro cell hcell s hs hscell
    have hcell' := mem_singularCells_iff.mp hcell
    exact
      separation.cell_point_unique cell hcell'.1 s hs hscell (pointOfCell cell)
        (point_spec cell hcell'.2).1 (point_spec cell hcell'.2).2
  · intro cell hcell other hother heq
    have hcell' := mem_singularCells_iff.mp hcell
    have hother' := mem_singularCells_iff.mp hother
    exact
      separation.point_cell_unique (pointOfCell cell) (point_spec cell hcell'.2).1 cell hcell'.1
        (point_spec cell hcell'.2).2 other hother'.1 (heq ▸ (point_spec other hother'.2).2)
  · intro s hs
    obtain ⟨cell, hcell, hscell⟩ := separation.point_covered s hs
    have hcontains : CellContainsSingularity S cell := ⟨s, hs, hscell⟩
    refine ⟨cell, mem_singularCells_iff.mpr ⟨hcell, hcontains⟩, ?_⟩
    exact
      (separation.cell_point_unique cell hcell s hs hscell (pointOfCell cell)
          (point_spec cell hcontains).1 (point_spec cell hcontains).2).symm

/-- Interior grid separation directly supplies the singular-cell assignment. -/
noncomputable def GridInteriorSeparation.toAssignment {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : GridInteriorSeparation S cells) : SingularCellAssignment S cells :=
  interior.toSeparation.toAssignment

/-- The set of points of `S` assigned to singular cells is exactly `S` itself. -/
theorem SingularCellAssignment.image_pointOfCell_eq {S : Finset ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : SingularCellAssignment S cells) :
    (finiteSingularCells S cells).image assignment.pointOfCell = S := by
  apply Finset.Subset.antisymm
  · intro s hs
    obtain ⟨cell, hcell, heq⟩ := Finset.mem_image.mp hs
    exact heq ▸ assignment.point_mem_ledger cell hcell
  · intro s hs
    obtain ⟨cell, hcell, heq⟩ := assignment.point_covered s hs
    exact Finset.mem_image.mpr ⟨cell, hcell, heq⟩

/--
**the finite residue theorem**: the finite punctured-rectangle residue theorem. Given a
grid-subdivision decomposition
of the outer rectangle boundary integral into cell boundary integrals (`hsum`, produced by the
caller from `RectangleGeometry.rectangleBoundaryIntegral_eq_gridSubdivision` and
`RectangleGeometry.rectangleGridSubdivision_eq_sum_toFinset`), a kernel `f` differentiable off `S`
*within each
listed cell* (a local hypothesis, not global: `f` need not be differentiable anywhere outside the
outer rectangle, which matters once `S` is a rectangle-relative ledger like
`DirichletLFunction.dirichletLFunctionSingularitiesInRectangle` that says nothing about
singularities elsewhere in the
plane), a singular-cell assignment, and each singular cell's boundary integral already identified
with `res` at its assigned point, the outer boundary integral is `Σ s ∈ S, res s`. (Any `2πi`
factor is folded into `res` by the caller.)
-/
theorem rectangleBoundaryIntegral_eq_sum_res (f res : ℂ → ℂ) (S : Finset ℂ) (cells : Finset (ℂ × ℂ))
    (z w : ℂ) (assignment : SingularCellAssignment S cells)
    (hsum :
      rectangleBoundaryIntegral f z w = ∑ cell ∈ cells, rectangleBoundaryIntegral f cell.1 cell.2)
    (hdiff :
      ∀ cell ∈ cells,
        ∀ x ∈ Rectangle.rectangleClosedBox cell.1 cell.2, x ∉ S → DifferentiableAt ℂ f x)
    (hsingular_res :
      ∀ cell ∈ finiteSingularCells S cells,
        rectangleBoundaryIntegral f cell.1 cell.2 = res (assignment.pointOfCell cell)) :
    rectangleBoundaryIntegral f z w = ∑ s ∈ S, res s := by
  have hregular_zero :
    ∀ cell ∈ finiteRegularCells S cells, rectangleBoundaryIntegral f cell.1 cell.2 = 0 := by
    intro cell hcell
    have hcell' := mem_regularCells_iff.mp hcell
    have hdisjoint : ¬CellContainsSingularity S cell := hcell'.2
    apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    intro x hx
    apply (hdiff cell hcell'.1 x hx ?_).differentiableWithinAt
    intro hxS
    exact hdisjoint ⟨x, hxS, hx⟩
  have hcombine :=
    sum_finiteRegularCells_add_sum_finiteSingularCells S cells
      (fun cell ↦ rectangleBoundaryIntegral f cell.1 cell.2)
  rw [Finset.sum_congr rfl hregular_zero, Finset.sum_const_zero, zero_add,
    Finset.sum_congr rfl hsingular_res] at hcombine
  rw [hsum, ← hcombine, ← Finset.sum_image assignment.distinct_points,
    assignment.image_pointOfCell_eq]

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry
