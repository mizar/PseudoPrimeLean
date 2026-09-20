/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary

/-!
# Singularity geometry for Riemann-zeta contour rectangles

This file collects the purely geometric bookkeeping needed to run a rectangular contour
argument around `riemannZeta`: the finite singularity ledger (zero, one, and the zeta zeros
in a rectangle), regular/singular cell filtering, and the abstract grid/singularity
separation certificates that let a concrete grid construction be plugged in independently.
None of the material here refers to any particular contour kernel; it is reused unchanged by
every explicit-formula argument built over `riemannZeta`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/--
The regular locus for Riemann-zeta contour integration: the plane minus zero, one, and every
zeta zero.  This is the domain supplied to Cauchy-integral arguments over `riemannZeta`.
-/
def riemannZetaRegularSet : Set ℂ :=
  {s | s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0}

/--
A rectangle is regular for Riemann-zeta contour work when its entire closed box avoids zero, one,
and all zeta zeros.
-/
def RiemannZetaRectangleIsRegular (z w : ℂ) : Prop :=
  (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ riemannZetaRegularSet

/-- The regular locus is open. -/
theorem isOpen_riemannZetaRegularSet : IsOpen riemannZetaRegularSet := by
  have hzeta : IsOpen (({1}ᶜ : Set ℂ) ∩ riemannZeta ⁻¹' ({0}ᶜ : Set ℂ)) :=
    differentiableOn_riemannZeta.continuousOn.isOpen_inter_preimage isOpen_compl_singleton
      isOpen_compl_singleton
  rw [show
      riemannZetaRegularSet = ({0}ᶜ : Set ℂ) ∩ (({1}ᶜ : Set ℂ) ∩ riemannZeta ⁻¹' ({0}ᶜ : Set ℂ))
      by
      ext s
      simp only [riemannZetaRegularSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_singleton_iff, Set.mem_preimage]]
  exact isOpen_compl_singleton.inter hzeta

def centeredSquarePuncturedRegion (c : ℂ) (R ρ : ℝ) : Set ℂ :=
  Rectangle.rectangleClosedBox (RectangleGeometry.centeredSquareLower c R)
      (RectangleGeometry.centeredSquareUpper c R) \
    Metric.ball c ρ

/-- The finite singularity ledger for a contour rectangle: its zeta zeros together with zero and
one whenever those lie in the rectangle. -/
noncomputable def riemannZetaSingularitiesInRectangle (z w : ℂ) : Finset ℂ := by
  classical
    exact
    riemannZetaZerosInAnyRectangle z w ∪
      (if (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w then {0} else ∅) ∪
      (if (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w then {1} else ∅)

/-- Membership in the finite singularity ledger has its expected geometric specification. -/
theorem mem_riemannZetaSingularitiesInRectangle_iff {z w s : ℂ} :
    s ∈ riemannZetaSingularitiesInRectangle z w ↔
      s ∈ Rectangle.rectangleClosedBox z w ∧ (s = 0 ∨ s = 1 ∨ riemannZeta s = 0) := by
  rw [riemannZetaSingularitiesInRectangle, Finset.mem_union, Finset.mem_union]
  rw [mem_riemannZetaZerosInAnyRectangle_iff]
  by_cases hzero : (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w <;>
    by_cases hone : (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w <;>
    simp only [hzero, reduceIte, Finset.mem_singleton, hone, Finset.notMem_empty, or_false,
      and_congr_right_iff] <;>
    aesop

/-- A point inside the contour rectangle but outside its finite ledger is kernel-regular. -/
theorem mem_riemannZetaRegularSet_of_not_mem_singularities {z w s : ℂ}
    (hrect : s ∈ Rectangle.rectangleClosedBox z w)
    (hnot : s ∉ riemannZetaSingularitiesInRectangle z w) : s ∈ riemannZetaRegularSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    exact hnot (mem_riemannZetaSingularitiesInRectangle_iff.mpr ⟨hrect, Or.inl hs⟩)
  · intro hs
    exact hnot (mem_riemannZetaSingularitiesInRectangle_iff.mpr ⟨hrect, Or.inr (Or.inl hs)⟩)
  · intro hs
    exact hnot (mem_riemannZetaSingularitiesInRectangle_iff.mpr ⟨hrect, Or.inr (Or.inr hs)⟩)

/-- A horizontal segment avoiding all ledger imaginary coordinates is kernel-regular. -/
theorem horizontal_segment_subset_riemannZetaRegularSet {z w : ℂ} {c a b : ℝ}
    (ha : a ∈ Set.uIcc z.re w.re) (hb : b ∈ Set.uIcc z.re w.re) (hc : c ∈ Set.uIcc z.im w.im)
    (havoid : ∀ s ∈ riemannZetaSingularitiesInRectangle z w, s.im ≠ c) :
    ∀ t ∈ Set.uIcc a b, t + c * Complex.I ∈ riemannZetaRegularSet := by
  intro t ht
  have hrect : (t : ℂ) + c * Complex.I ∈ Rectangle.rectangleClosedBox z w := by
    exact
      ⟨by
        simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using Set.uIcc_subset_uIcc ha hb ht,
        by
        simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
          zero_add] using hc⟩
  apply mem_riemannZetaRegularSet_of_not_mem_singularities hrect
  intro hs
  exact
    havoid _ hs
      (by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add])

/-- A vertical segment avoiding all ledger real coordinates is kernel-regular. -/
theorem vertical_segment_subset_riemannZetaRegularSet {z w : ℂ} {c a b : ℝ}
    (hc : c ∈ Set.uIcc z.re w.re) (ha : a ∈ Set.uIcc z.im w.im) (hb : b ∈ Set.uIcc z.im w.im)
    (havoid : ∀ s ∈ riemannZetaSingularitiesInRectangle z w, s.re ≠ c) :
    ∀ t ∈ Set.uIcc a b, c + t * Complex.I ∈ riemannZetaRegularSet := by
  intro t ht
  have hrect : (c : ℂ) + t * Complex.I ∈ Rectangle.rectangleClosedBox z w := by
    exact
      ⟨by
        simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using hc,
        by
        simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
          zero_add] using Set.uIcc_subset_uIcc ha hb ht⟩
  apply mem_riemannZetaRegularSet_of_not_mem_singularities hrect
  intro hs
  exact
    havoid _ hs
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero])

/-- The separated zero, one, and zeta-zero contributions of a singularity-valued sum. -/
noncomputable def riemannZetaSplitSingularitySum {M : Type*} [AddCommMonoid M] (z w : ℂ)
    (value : ℂ → M) : M := by
  classical
    exact
    (if (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w then value 0 else 0) +
      (if (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w then value 1 else 0) +
      ∑ ρ ∈ riemannZetaZerosInAnyRectangle z w, value ρ

/--
A sum over the full singularity ledger splits into the Mellin poles and the zeta-zero ledger.

Zeta has no zero at zero or one, so the three finite pieces are disjoint.  The statement is
generic in the additive target and is reused for both contour kernels.
-/
theorem sum_riemannZetaSingularitiesInRectangle {M : Type*} [AddCommMonoid M] (z w : ℂ)
    (value : ℂ → M) :
    (∑ s ∈ riemannZetaSingularitiesInRectangle z w, value s) =
      riemannZetaSplitSingularitySum z w value := by
  classical
  have hzero : (0 : ℂ) ∉ riemannZetaZerosInAnyRectangle z w := by
    intro hmem
    exact ne_zero_of_mem_riemannZetaZerosInAnyRectangle hmem rfl
  have hone : (1 : ℂ) ∉ riemannZetaZerosInAnyRectangle z w := by
    intro hmem
    exact ne_one_of_mem_riemannZetaZerosInAnyRectangle hmem rfl
  have honeInsert : (1 : ℂ) ∉ insert 0 (riemannZetaZerosInAnyRectangle z w) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact one_ne_zero h
    · exact hone h
  by_cases hzeroRect : (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w <;>
    by_cases honeRect : (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w <;>
    simp only [riemannZetaSingularitiesInRectangle, hzeroRect, reduceIte, Finset.union_singleton,
      honeRect, Finset.sum_insert hzero, Finset.sum_insert honeInsert,
      riemannZetaSplitSingularitySum, add_assoc, Finset.union_empty, Finset.union_singleton,
      add_comm, add_left_comm, zero_add, add_zero]
  all_goals aesop

/--
A subrectangle disjoint from the enclosing rectangle's singularity ledger is regular.

The subset hypothesis ensures that any singular point of the cell would occur in the enclosing
finite ledger.  Set disjointness then excludes zero, one, and every zeta zero simultaneously.  This
is the bridge from a geometric grid-cell certificate to the Cauchy--Goursat regularity hypothesis.
-/
theorem riemannZetaRectangleIsRegular_of_disjoint_singularities {z w a b : ℂ}
    (hsubset : Rectangle.rectangleClosedBox a b ⊆ Rectangle.rectangleClosedBox z w)
    (hdisjoint :
      Disjoint (Rectangle.rectangleClosedBox a b)
        (riemannZetaSingularitiesInRectangle z w : Set ℂ)) :
    RiemannZetaRectangleIsRegular a b := by
  intro s hs
  have exclude (hsingular : s = 0 ∨ s = 1 ∨ riemannZeta s = 0) : False := by
    have hledger : s ∈ riemannZetaSingularitiesInRectangle z w :=
      mem_riemannZetaSingularitiesInRectangle_iff.mpr ⟨hsubset hs, hsingular⟩
    exact Set.disjoint_left.mp hdisjoint hs hledger
  refine ⟨?_, ?_, ?_⟩
  · intro hs0
    exact exclude (Or.inl hs0)
  · intro hs1
    exact exclude (Or.inr (Or.inl hs1))
  · intro hzeta
    exact exclude (Or.inr (Or.inr hzeta))

/--
A finite ledger of rectangular cells certified to avoid every singularity of an outer rectangle.

Each cell is represented by its pair of opposite complex corners.  `cell_subset` places its closed
rectangle inside the outer one, while `cell_disjoint` excludes the outer finite singularity ledger.
Together these invariants make every listed cell suitable for the rectangular Cauchy--Goursat
theorem.  A later geometric layer will add coverage of the punctured rectangle.
-/
structure RiemannZetaRegularCellLedger (z w : ℂ) where
  cells : Finset (ℂ × ℂ)
  cell_subset :
    ∀ cell ∈ cells, Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w
  cell_disjoint :
    ∀ cell ∈ cells,
      Disjoint (Rectangle.rectangleClosedBox cell.1 cell.2)
        (riemannZetaSingularitiesInRectangle z w : Set ℂ)

/-- A cell contains a singularity catalogued in the enclosing rectangle. -/
def RiemannZetaCellContainsSingularity (z w : ℂ) (cell : ℂ × ℂ) : Prop :=
  ∃ s ∈ riemannZetaSingularitiesInRectangle z w, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2

/-- The cells avoiding every singularity of the enclosing rectangle. -/
noncomputable def riemannZetaRegularCells (z w : ℂ) (cells : Finset (ℂ × ℂ)) : Finset (ℂ × ℂ) := by
  classical exact cells.filter fun cell ↦ ¬RiemannZetaCellContainsSingularity z w cell

/-- The cells containing at least one singularity of the enclosing rectangle. -/
noncomputable def riemannZetaSingularCells (z w : ℂ) (cells : Finset (ℂ × ℂ)) : Finset (ℂ × ℂ) := by
  classical exact cells.filter fun cell ↦ RiemannZetaCellContainsSingularity z w cell

/-- Membership in the regular-cell filter has its expected specification. -/
theorem mem_riemannZetaRegularCells_iff {z w : ℂ} {cells : Finset (ℂ × ℂ)} {cell : ℂ × ℂ} :
    cell ∈ riemannZetaRegularCells z w cells ↔
      cell ∈ cells ∧ ¬RiemannZetaCellContainsSingularity z w cell := by
  classical simp only [riemannZetaRegularCells, Finset.mem_filter]

/-- Membership in the singular-cell filter has its expected specification. -/
theorem mem_riemannZetaSingularCells_iff {z w : ℂ} {cells : Finset (ℂ × ℂ)} {cell : ℂ × ℂ} :
    cell ∈ riemannZetaSingularCells z w cells ↔
      cell ∈ cells ∧ RiemannZetaCellContainsSingularity z w cell := by
  classical simp only [riemannZetaSingularCells, Finset.mem_filter]

/-- The regular and singular filters partition any finite cell sum. -/
theorem sum_regularCells_add_sum_singularCells {M : Type*} [AddCommMonoid M] (z w : ℂ)
    (cells : Finset (ℂ × ℂ)) (value : ℂ × ℂ → M) :
    (∑ cell ∈ riemannZetaRegularCells z w cells, value cell) +
        ∑ cell ∈ riemannZetaSingularCells z w cells, value cell =
      ∑ cell ∈ cells, value cell := by
  classical
  unfold riemannZetaRegularCells riemannZetaSingularCells
  rw [add_comm, Finset.sum_filter_add_sum_filter_not]

/--
Cells inside an outer rectangle yield a regular-cell ledger after filtering out singular cells.
-/
noncomputable def riemannZetaRegularCellLedgerOfCells (z w : ℂ) (cells : Finset (ℂ × ℂ))
    (hsubset :
      ∀ cell ∈ cells,
        Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w) :
    RiemannZetaRegularCellLedger z w := by
  classical
  refine ⟨riemannZetaRegularCells z w cells, ?_, ?_⟩
  · intro cell hcell
    exact hsubset cell (mem_riemannZetaRegularCells_iff.mp hcell).1
  · intro cell hcell
    apply Set.disjoint_left.mpr
    intro s hscell hsledger
    exact (mem_riemannZetaRegularCells_iff.mp hcell).2 ⟨s, hsledger, hscell⟩

/--
A finite assignment of exactly one catalogued singularity to every singular grid cell.

`pointOfCell` selects the point assigned to a cell.  The first three invariants state that this is
the unique enclosing-ledger point inside that cell.  `distinct_points` prevents two different
singular cells from representing the same point, and `point_covered` ensures that every enclosing
singularity occurs.  Thus the singular cells and the finite singularity ledger are in bijection,
without committing the geometric layer to a particular construction of the grid.
-/
structure RiemannZetaSingularCellAssignment (z w : ℂ) (cells : Finset (ℂ × ℂ)) where
  pointOfCell : ℂ × ℂ → ℂ
  point_mem_ledger :
    ∀ cell ∈ riemannZetaSingularCells z w cells,
      pointOfCell cell ∈ riemannZetaSingularitiesInRectangle z w
  point_mem_cell :
    ∀ cell ∈ riemannZetaSingularCells z w cells,
      pointOfCell cell ∈ Rectangle.rectangleClosedBox cell.1 cell.2
  point_unique :
    ∀ cell ∈ riemannZetaSingularCells z w cells,
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s = pointOfCell cell
  distinct_points :
    ∀ cell ∈ riemannZetaSingularCells z w cells,
      ∀ other ∈ riemannZetaSingularCells z w cells,
        pointOfCell cell = pointOfCell other → cell = other
  point_covered :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      ∃ cell ∈ riemannZetaSingularCells z w cells, pointOfCell cell = s

/--
Geometric separation conditions making grid cells and singularities correspond bijectively.

`cell_point_unique` says that one cell contains at most one catalogued singularity.
`point_cell_unique` says that one catalogued singularity belongs to at most one listed cell; this
excludes placement on shared grid edges.  `point_covered` places every catalogued singularity in a
listed cell.  These three conditions construct `RiemannZetaSingularCellAssignment` canonically via
finite-choice-independent unique witnesses.
-/
structure RiemannZetaGridSingularitySeparation (z w : ℂ) (cells : Finset (ℂ × ℂ)) where
  cell_point_unique :
    ∀ cell ∈ cells,
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          ∀ t ∈ riemannZetaSingularitiesInRectangle z w,
            t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s = t
  point_cell_unique :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      ∀ cell ∈ cells,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          ∀ other ∈ cells, s ∈ Rectangle.rectangleClosedBox other.1 other.2 → cell = other
  point_covered :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      ∃ cell ∈ cells, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2

/--
Interior geometric conditions sufficient for grid/singularity separation.

Each cell contains at most one ledger point.  Every ledger point lying in a listed closed cell is
required to lie in its open rectangle, expressing avoidance of all grid edges.  Distinct listed
open rectangles are disjoint, and every ledger point is covered.  These conditions isolate the
two geometric tasks for a concrete grid: separating points and choosing cuts away from them.
-/
structure RiemannZetaGridInteriorSeparation (z w : ℂ) (cells : Finset (ℂ × ℂ)) where
  cell_point_unique :
    ∀ cell ∈ cells,
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          ∀ t ∈ riemannZetaSingularitiesInRectangle z w,
            t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 → s = t
  point_mem_open :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      ∀ cell ∈ cells,
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
          s ∈ RectangleGeometry.rectangleOpenBox cell.1 cell.2
  open_disjoint :
    ∀ cell ∈ cells,
      ∀ other ∈ cells,
        cell ≠ other →
          Disjoint (RectangleGeometry.rectangleOpenBox cell.1 cell.2)
            (RectangleGeometry.rectangleOpenBox other.1 other.2)
  point_covered :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      ∃ cell ∈ cells, s ∈ Rectangle.rectangleClosedBox cell.1 cell.2

/-- Interior separation conditions imply the abstract grid/singularity separation certificate. -/
theorem RiemannZetaGridInteriorSeparation.toSeparation {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : RiemannZetaGridInteriorSeparation z w cells) :
    RiemannZetaGridSingularitySeparation z w cells := by
  refine ⟨interior.cell_point_unique, ?_, interior.point_covered⟩
  intro s hs cell hcell hscell other hother hsother
  by_contra hne
  exact
    Set.disjoint_left.mp (interior.open_disjoint cell hcell other hother hne)
      (interior.point_mem_open s hs cell hcell hscell)
      (interior.point_mem_open s hs other hother hsother)

/-- Geometric cell/singularity separation induces the singular-cell assignment ledger. -/
noncomputable def RiemannZetaGridSingularitySeparation.toAssignment {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (separation : RiemannZetaGridSingularitySeparation z w cells) :
    RiemannZetaSingularCellAssignment z w cells := by
  classical
  let pointOfCell : ℂ × ℂ → ℂ := fun cell ↦
    Classical.epsilon fun s ↦
      s ∈ riemannZetaSingularitiesInRectangle z w ∧ s ∈ Rectangle.rectangleClosedBox cell.1 cell.2
  have point_spec (cell : ℂ × ℂ) (hcell : RiemannZetaCellContainsSingularity z w cell) :
    pointOfCell cell ∈ riemannZetaSingularitiesInRectangle z w ∧
      pointOfCell cell ∈ Rectangle.rectangleClosedBox cell.1 cell.2 := by
    exact Classical.epsilon_spec hcell
  refine ⟨pointOfCell, ?_, ?_, ?_, ?_, ?_⟩
  · intro cell hcell
    exact (point_spec cell (mem_riemannZetaSingularCells_iff.mp hcell).2).1
  · intro cell hcell
    exact (point_spec cell (mem_riemannZetaSingularCells_iff.mp hcell).2).2
  · intro cell hcell s hs hscell
    have hcell' := mem_riemannZetaSingularCells_iff.mp hcell
    exact
      separation.cell_point_unique cell hcell'.1 s hs hscell (pointOfCell cell)
        (point_spec cell hcell'.2).1 (point_spec cell hcell'.2).2
  · intro cell hcell other hother heq
    have hcell' := mem_riemannZetaSingularCells_iff.mp hcell
    have hother' := mem_riemannZetaSingularCells_iff.mp hother
    exact
      separation.point_cell_unique (pointOfCell cell) (point_spec cell hcell'.2).1 cell hcell'.1
        (point_spec cell hcell'.2).2 other hother'.1 (heq ▸ (point_spec other hother'.2).2)
  · intro s hs
    obtain ⟨cell, hcell, hscell⟩ := separation.point_covered s hs
    have hcontains : RiemannZetaCellContainsSingularity z w cell := ⟨s, hs, hscell⟩
    refine ⟨cell, mem_riemannZetaSingularCells_iff.mpr ⟨hcell, hcontains⟩, ?_⟩
    exact
      (separation.cell_point_unique cell hcell s hs hscell (pointOfCell cell)
          (point_spec cell hcontains).1 (point_spec cell hcontains).2).symm

/-- Interior grid separation directly supplies the singular-cell assignment. -/
noncomputable def RiemannZetaGridInteriorSeparation.toAssignment {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : RiemannZetaGridInteriorSeparation z w cells) :
    RiemannZetaSingularCellAssignment z w cells :=
  interior.toSeparation.toAssignment

/-- A certified singular cell contains exactly its assigned enclosing-ledger point. -/
theorem RiemannZetaSingularCellAssignment.existsUnique_point_in_cell {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {cell : ℂ × ℂ} (hcell : cell ∈ riemannZetaSingularCells z w cells) :
    ∃! s : ℂ,
      s ∈ riemannZetaSingularitiesInRectangle z w ∧
        s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 := by
  refine
    ⟨assignment.pointOfCell cell,
      ⟨assignment.point_mem_ledger cell hcell, assignment.point_mem_cell cell hcell⟩, ?_⟩
  intro s hs
  exact assignment.point_unique cell hcell s hs.1 hs.2

/--
A subrectangle of a singular cell is regular when it excludes the cell's assigned singularity.

Every catalogued singularity in the parent cell equals its assigned point.  Hence containment in
the parent and exclusion of that one point make the subrectangle disjoint from the entire finite
singularity ledger.  The standard ledger-disjointness criterion then supplies kernel regularity.
-/
theorem RiemannZetaSingularCellAssignment.subcell_isRegular {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : RiemannZetaSingularCellAssignment z w cells) {parent child : ℂ × ℂ}
    (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hchildSubset :
      Rectangle.rectangleClosedBox child.1 child.2 ⊆ Rectangle.rectangleClosedBox parent.1 parent.2)
    (hexclude : assignment.pointOfCell parent ∉ Rectangle.rectangleClosedBox child.1 child.2) :
    RiemannZetaRectangleIsRegular child.1 child.2 := by
  apply riemannZetaRectangleIsRegular_of_disjoint_singularities
  · exact hchildSubset.trans hparentSubset
  · apply Set.disjoint_left.mpr
    intro s hschild hsledger
    have heq := assignment.point_unique parent hparent s hsledger (hchildSubset hschild)
    exact hexclude (heq ▸ hschild)

/-- A point of a singular parent cell is kernel-regular unless it is the assigned singularity. -/
theorem RiemannZetaSingularCellAssignment.mem_regular_of_mem_parent_of_ne {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {s : ℂ} (hs : s ∈ Rectangle.rectangleClosedBox parent.1 parent.2)
    (hne : s ≠ assignment.pointOfCell parent) : s ∈ riemannZetaRegularSet := by
  apply mem_riemannZetaRegularSet_of_not_mem_singularities (hparentSubset hs)
  intro hsledger
  exact hne (assignment.point_unique parent hparent s hsledger hs)

/-- A centered square with a positive-radius central ball removed is regular in its parent cell. -/
theorem RiemannZetaSingularCellAssignment.centeredSquarePuncturedRegion_subset_regularSet {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hre : parent.1.re < parent.2.re) (him : parent.1.im < parent.2.im) {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) R ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2) :
    centeredSquarePuncturedRegion (assignment.pointOfCell parent) R ρ ⊆ riemannZetaRegularSet := by
  intro s hs
  apply assignment.mem_regular_of_mem_parent_of_ne hparent hparentSubset
  · exact RectangleGeometry.centeredSquare_closedBox_subset_parent hre him hR hball hs.1
  · intro heq
    subst s
    exact hs.2 (Metric.mem_ball_self hρ)

/-- The rectangle boundary avoids every singularity of the two Riemann-zeta kernels. -/
def RiemannZetaRectangleBoundaryIsRegular (z w : ℂ) : Prop :=
  RectangleGeometry.rectangleClosedBoxBoundary z w ⊆ riemannZetaRegularSet

/-- Every noncentral cell of a strict `3 × 3` puncture grid is kernel-regular. -/
theorem RiemannZetaSingularCellAssignment.threeByThree_noncentral_isRegular {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {a b : ℂ} (hzare : parent.1.re < a.re) (habre : a.re < b.re) (hbwre : b.re < parent.2.re)
    (hzaim : parent.1.im < a.im) (habim : a.im < b.im) (hbwim : b.im < parent.2.im)
    (hpoint : assignment.pointOfCell parent ∈ RectangleGeometry.rectangleOpenBox a b)
    {child : ℂ × ℂ}
    (hchild :
      child ∈ RectangleGeometry.rectangleGridCells parent.1 parent.2 [a.re, b.re] [a.im, b.im])
    (hne : child ≠ (a, b)) : RiemannZetaRectangleIsRegular child.1 child.2 := by
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
  have hchildSubset :
    Rectangle.rectangleClosedBox child.1 child.2 ⊆ Rectangle.rectangleClosedBox parent.1 parent.2 :=
    RectangleGeometry.rectangleGridCells_closedBox_subset hxcuts hycuts child hchild
  apply assignment.subcell_isRegular hparent hparentSubset hchildSubset
  exact
    RectangleGeometry.not_mem_noncentral_threeByThreeGridCell hzare habre hbwre hzaim habim hbwim
      hpoint hchild hne

/-- The noncentral-cell regularity theorem in the finite-set form used by contour contraction. -/
theorem RiemannZetaSingularCellAssignment.threeByThree_surrounding_regular {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {a b : ℂ} (hzare : parent.1.re < a.re) (habre : a.re < b.re) (hbwre : b.re < parent.2.re)
    (hzaim : parent.1.im < a.im) (habim : a.im < b.im) (hbwim : b.im < parent.2.im)
    (hpoint : assignment.pointOfCell parent ∈ RectangleGeometry.rectangleOpenBox a b) :
    ∀
      child ∈
        (RectangleGeometry.rectangleGridCells parent.1 parent.2 [a.re, b.re] [a.im, b.im]).toFinset,
      child ≠ (a, b) → RiemannZetaRectangleIsRegular child.1 child.2 := by
  intro child hchild hne
  apply
    assignment.threeByThree_noncentral_isRegular hparent hparentSubset hzare habre hbwre hzaim habim
      hbwim hpoint
  · simpa only [List.mem_toFinset] using hchild
  · exact hne

/-- Interior separation places each assigned singularity in its cell's open rectangle. -/
theorem RiemannZetaGridInteriorSeparation.pointOfCell_mem_open {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (interior : RiemannZetaGridInteriorSeparation z w cells) {cell : ℂ × ℂ}
    (hcell : cell ∈ riemannZetaSingularCells z w cells) :
    interior.toAssignment.pointOfCell cell ∈ RectangleGeometry.rectangleOpenBox cell.1 cell.2 := by
  apply interior.point_mem_open
  · exact interior.toAssignment.point_mem_ledger cell hcell
  · exact (mem_riemannZetaSingularCells_iff.mp hcell).1
  · exact interior.toAssignment.point_mem_cell cell hcell

/-- Every assigned singularity has a positive closed ball contained in its open cell. -/
theorem RiemannZetaGridInteriorSeparation.exists_closedBall_pointOfCell_subset_open {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (interior : RiemannZetaGridInteriorSeparation z w cells) {cell : ℂ × ℂ}
    (hcell : cell ∈ riemannZetaSingularCells z w cells) :
    ∃ ε : ℝ,
      0 < ε ∧
        Metric.closedBall (interior.toAssignment.pointOfCell cell) ε ⊆
          RectangleGeometry.rectangleOpenBox cell.1 cell.2 := by
  exact
    RectangleGeometry.exists_closedBall_subset_rectangleOpenBox
      (interior.pointOfCell_mem_open hcell)

/-- All assigned singularities admit one common positive radius contained in their open cells. -/
theorem RiemannZetaGridInteriorSeparation.exists_common_cell_radius {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (interior : RiemannZetaGridInteriorSeparation z w cells) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ cell ∈ riemannZetaSingularCells z w cells,
          Metric.closedBall (interior.toAssignment.pointOfCell cell) ε ⊆
            RectangleGeometry.rectangleOpenBox cell.1 cell.2 := by
  apply RectangleGeometry.Finset.exists_common_closedBall_subset
  intro cell hcell
  exact interior.exists_closedBall_pointOfCell_subset_open hcell

/-- A singular-cell sum can be reindexed by the finite enclosing singularity ledger. -/
theorem RiemannZetaSingularCellAssignment.sum_pointOfCell {M : Type*} [AddCommMonoid M] {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    (value : ℂ → M) :
    (∑ cell ∈ riemannZetaSingularCells z w cells, value (assignment.pointOfCell cell)) =
      ∑ s ∈ riemannZetaSingularitiesInRectangle z w, value s := by
  apply Finset.sum_bij (fun cell _ ↦ assignment.pointOfCell cell)
  · intro cell hcell
    exact assignment.point_mem_ledger cell hcell
  · intro cell hcell other hother heq
    exact assignment.distinct_points cell hcell other hother heq
  · intro s hs
    obtain ⟨cell, hcell, hpoint⟩ := assignment.point_covered s hs
    exact ⟨cell, hcell, hpoint⟩
  · intro cell hcell
    rfl

/-- Every cell in a regular-cell ledger is a regular zeta-kernel rectangle. -/
theorem RiemannZetaRegularCellLedger.cell_isRegular {z w : ℂ}
    (ledger : RiemannZetaRegularCellLedger z w) {cell : ℂ × ℂ} (hcell : cell ∈ ledger.cells) :
    RiemannZetaRectangleIsRegular cell.1 cell.2 := by
  exact
    riemannZetaRectangleIsRegular_of_disjoint_singularities (ledger.cell_subset cell hcell)
      (ledger.cell_disjoint cell hcell)

/-- A regular contour boundary contains none of the finitely catalogued singularities. -/
theorem not_mem_rectangleClosedBoxBoundary_of_mem_riemannZetaSingularities {z w s : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    (hs : s ∈ riemannZetaSingularitiesInRectangle z w) :
    s ∉ RectangleGeometry.rectangleClosedBoxBoundary z w := by
  intro hboundary
  have hsregular := hregular hboundary
  rw [mem_riemannZetaSingularitiesInRectangle_iff] at hs
  rcases hs.2 with rfl | rfl | hzeta
  · exact hsregular.1 rfl
  · exact hsregular.2.1 rfl
  · exact hsregular.2.2 hzeta

/-- A catalogued singularity lies in the open rectangle when the outer boundary is regular. -/
theorem mem_rectangleOpenBox_of_mem_riemannZetaSingularities {z w s : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    (hs : s ∈ riemannZetaSingularitiesInRectangle z w) :
    s ∈ RectangleGeometry.rectangleOpenBox z w := by
  have hsclosed := (mem_riemannZetaSingularitiesInRectangle_iff.mp hs).1
  by_contra hnot
  exact
    not_mem_rectangleClosedBoxBoundary_of_mem_riemannZetaSingularities hregular hs
      ⟨hsclosed, by simpa only [RectangleGeometry.rectangleOpenBox] using hnot⟩

/-- Every catalogued singularity has positive clearance from a regular contour boundary. -/
theorem riemannZetaSingularityBoundaryClearance_pos {z w s : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    (hs : s ∈ riemannZetaSingularitiesInRectangle z w) :
    0 < RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w := by
  have hnotmem := not_mem_rectangleClosedBoxBoundary_of_mem_riemannZetaSingularities hregular hs
  have hinf : 0 < Metric.infDist s (RectangleGeometry.rectangleClosedBoxBoundary z w) :=
    ((RectangleGeometry.isClosed_rectangleClosedBoxBoundary z w).notMem_iff_infDist_pos
          (RectangleGeometry.nonempty_rectangleClosedBoxBoundary z w)).mp
      hnotmem
  exact div_pos hinf (by norm_num only)

/-- The clearance radius is strictly smaller than the distance to every boundary point. -/
theorem riemannZetaSingularityBoundaryClearance_lt_dist {z w s y : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    (hs : s ∈ riemannZetaSingularitiesInRectangle z w)
    (hy : y ∈ RectangleGeometry.rectangleClosedBoxBoundary z w) :
    RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w < dist s y := by
  have hpos := riemannZetaSingularityBoundaryClearance_pos hregular hs
  have hhalf :
    RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w <
      Metric.infDist s (RectangleGeometry.rectangleClosedBoxBoundary z w) := by
    unfold RectangleGeometry.rectangleClosedBoxBoundaryClearance at hpos ⊢
    linarith
  exact hhalf.trans_le (Metric.infDist_le_dist_of_mem hy)

/-- A finite singularity ledger admits one positive clearance shared by all its points. -/
theorem exists_common_riemannZetaSingularityBoundaryClearance {z w : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
          ε < RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w := by
  classical
  let S := riemannZetaSingularitiesInRectangle z w
  by_cases hS : S.Nonempty
  · let values := S.image fun s ↦ RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w
    have hvalues : values.Nonempty := Finset.image_nonempty.mpr hS
    let m := values.min' hvalues
    have hmpos : 0 < m := by
      have hm := Finset.min'_mem values hvalues
      rcases Finset.mem_image.mp hm with ⟨s, hs, hsm⟩
      change 0 < values.min' hvalues
      rw [← hsm]
      exact riemannZetaSingularityBoundaryClearance_pos hregular hs
    refine ⟨m / 2, div_pos hmpos (by norm_num only), ?_⟩
    intro s hs
    have hsvalues : RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w ∈ values :=
      Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have hmle := Finset.min'_le values _ hsvalues
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro s hs
    exact (hS ⟨s, hs⟩).elim

/-- One radius separates the contour boundary and every pair of distinct singularities. -/
theorem exists_pairwise_disjoint_riemannZetaSingularityRadius {z w : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    ∃ ε : ℝ,
      0 < ε ∧
        (∀ s ∈ riemannZetaSingularitiesInRectangle z w,
          ∀ y ∈ RectangleGeometry.rectangleClosedBoxBoundary z w, ε < dist s y) ∧
        (∀ s ∈ riemannZetaSingularitiesInRectangle z w,
          ∀ t ∈ riemannZetaSingularitiesInRectangle z w, s ≠ t → 2 * ε < dist s t) := by
  classical
  let S := riemannZetaSingularitiesInRectangle z w
  let boundaryValues := S.image fun s ↦ RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w
  let pairValues := S.biUnion fun s ↦ (S.erase s).image fun t ↦ dist s t / 2
  let constraints := (boundaryValues ∪ pairValues) ∪ {1}
  have hconstraints : constraints.Nonempty :=
    ⟨1, by
      simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_union, true_or, constraints]⟩
  have hpositive : ∀ r ∈ constraints, 0 < r := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_union.mp hr with hr | hr
      · rcases Finset.mem_image.mp hr with ⟨s, hs, hsr⟩
        rw [← hsr]
        exact riemannZetaSingularityBoundaryClearance_pos hregular hs
      · rcases Finset.mem_biUnion.mp hr with ⟨s, hs, hr⟩
        rcases Finset.mem_image.mp hr with ⟨t, ht, htr⟩
        rw [← htr]
        have hts : t ≠ s := (Finset.mem_erase.mp ht).1
        exact div_pos (dist_pos.mpr hts.symm) (by norm_num only)
    · rw [Finset.mem_singleton.mp hr]
      norm_num only
  let m := constraints.min' hconstraints
  have hmpos : 0 < m := hpositive _ (Finset.min'_mem constraints hconstraints)
  refine ⟨m / 2, div_pos hmpos (by norm_num only), ?_, ?_⟩
  · intro s hs y hy
    have hmem : RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w ∈ constraints := by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩))
    have hmle := Finset.min'_le constraints _ hmem
    have hmhalf : m / 2 < RectangleGeometry.rectangleClosedBoxBoundaryClearance s z w := by linarith
    exact hmhalf.trans (riemannZetaSingularityBoundaryClearance_lt_dist hregular hs hy)
  · intro s hs t ht hst
    have hpair : dist s t / 2 ∈ pairValues := by
      apply Finset.mem_biUnion.mpr
      exact ⟨s, hs, Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨hst.symm, ht⟩, rfl⟩⟩
    have hmem : dist s t / 2 ∈ constraints :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hpair)
    have hmle := Finset.min'_le constraints _ hmem
    have hdist : 0 < dist s t := dist_pos.mpr hst
    linarith

/-- The closed rectangle with common-radius singularity balls removed. -/
noncomputable def riemannZetaPuncturedRectangle (z w : ℂ) (ε : ℝ) : Set ℂ :=
  Rectangle.rectangleClosedBox z w \
    ⋃ s ∈ (riemannZetaSingularitiesInRectangle z w : Set ℂ), Metric.closedBall s ε

/-- Removing nonnegative-radius balls around the ledger leaves only regular kernel points. -/
theorem riemannZetaPuncturedRectangle_subset_regularSet {z w : ℂ} {ε : ℝ} (hε : 0 ≤ ε) :
    riemannZetaPuncturedRectangle z w ε ⊆ riemannZetaRegularSet := by
  intro s hs
  have hsrect : s ∈ Rectangle.rectangleClosedBox z w := hs.1
  have exclude (hsingular : s = 0 ∨ s = 1 ∨ riemannZeta s = 0) : False := by
    have hsledger : s ∈ riemannZetaSingularitiesInRectangle z w :=
      mem_riemannZetaSingularitiesInRectangle_iff.mpr ⟨hsrect, hsingular⟩
    apply hs.2
    exact Set.mem_iUnion_of_mem s (Set.mem_iUnion_of_mem hsledger (Metric.mem_closedBall_self hε))
  refine ⟨?_, ?_, ?_⟩
  · intro hs0
    exact exclude (Or.inl hs0)
  · intro hs1
    exact exclude (Or.inr (Or.inl hs1))
  · intro hszeta
    exact exclude (Or.inr (Or.inr hszeta))

/-- A kernel regular off the assigned point has equal integrals on nested local circles. -/
theorem RiemannZetaSingularCellAssignment.circleIntegral_eq_of_le {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : RiemannZetaSingularCellAssignment z w cells) {parent : ℂ × ℂ}
    (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) R ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2)
    {f : ℂ → ℂ} (hdiff : DifferentiableOn ℂ f riemannZetaRegularSet) :
    (∮ u in C(assignment.pointOfCell parent, R), f u) =
      ∮ u in C(assignment.pointOfCell parent, r), f u := by
  let c := assignment.pointOfCell parent
  have hregular {s : ℂ} (hs : s ∈ Metric.closedBall c R) (hne : s ≠ c) :
    s ∈ riemannZetaRegularSet := by
    apply assignment.mem_regular_of_mem_parent_of_ne hparent hparentSubset
    · exact RectangleGeometry.rectangleOpenBox_subset_rectangleClosedBox _ _ (hball hs)
    · exact hne
  have hcontinuous : ContinuousOn f (Metric.closedBall c R \ Metric.ball c r) := by
    intro s hs
    have hne : s ≠ c := by
      intro hsc
      subst s
      exact hs.2 (Metric.mem_ball_self hr)
    have hsregular := hregular hs.1 hne
    exact
      ((hdiff s hsregular).differentiableAt
          (isOpen_riemannZetaRegularSet.mem_nhds hsregular)).continuousAt.continuousWithinAt
  have hdifferentiable :
    ∀ s ∈ (Metric.ball c R \ Metric.closedBall c r) \ (∅ : Set ℂ), DifferentiableAt ℂ f s := by
    intro s hs
    have hsregular :=
      hregular (Metric.ball_subset_closedBall hs.1.1) fun hsc =>
        hs.1.2 (hsc ▸ Metric.mem_closedBall_self hr.le)
    exact (hdiff s hsregular).differentiableAt (isOpen_riemannZetaRegularSet.mem_nhds hsregular)
  exact
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR Set.countable_empty
      hcontinuous hdifferentiable

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
