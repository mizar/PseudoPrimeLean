import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SingularityGeometry
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.GridCutConstruction

/-! # Kernel-independent zeta GridCuts -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/--
Construct strict grid cuts from the finite singularity ledger of a regular outer rectangle.

The real and imaginary lists are sorted coordinate-avoiding cuts selected between every ordered
pair of ledger coordinates, produced by the generic
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.generatedStrictGridCuts` construction applied
to the outer singularity ledger.  Boundary regularity supplies the openness hypothesis the generic
constructor needs.  The result is the concrete grid used to eliminate the finite geometric
assumptions from the contour decomposition.
-/
noncomputable def riemannZetaGeneratedStrictGridCuts (z w : ℂ) (hre : z.re < w.re)
    (him : z.im < w.im)
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    RectangleGeometry.StrictGridCuts z w :=
  RectangleGeometry.generatedStrictGridCuts
    (riemannZetaSingularitiesInRectangle z w) z w hre
    him fun _ hs ↦
    mem_rectangleOpenBox_of_mem_riemannZetaSingularities
      hregular hs

/--
The outer singularity ledger avoids every real and imaginary coordinate of a strict grid.

The predicate excludes both internal cuts and outer endpoints.  Boundary regularity will later
exclude the endpoints, while finite cut selection will exclude the internal coordinates.  Its
output is the shared-edge avoidance input for open-cell membership.
-/
def RiemannZetaGrid.LedgerAvoidsCoordinates {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w) : Prop :=
  ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
    s.re ∉ z.re :: grid.xcuts ++ [w.re] ∧ s.im ∉ z.im :: grid.ycuts ++ [w.im]

/-- The outer singularity ledger avoids every internal cut coordinate of a strict grid. -/
def RiemannZetaGrid.LedgerAvoidsCuts {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w) : Prop :=
  ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
    s.re ∉ grid.xcuts ∧ s.im ∉ grid.ycuts

/--
Internal cuts separate every pair of distinct singularity-ledger points in some coordinate.

For each ordered pair of distinct points, a real or imaginary cut lies strictly between their
corresponding coordinates in either orientation.  This condition prevents the pair from occupying
one open grid cell and supplies cell-level point uniqueness.
-/
def RiemannZetaGrid.LedgerPairsSeparatedByCuts {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w) : Prop :=
  ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
    ∀ t ∈ riemannZetaSingularitiesInRectangle z w,
      s ≠ t →
        (∃ u ∈ grid.xcuts, (s.re < u ∧ u < t.re) ∨ (t.re < u ∧ u < s.re)) ∨
          ∃ v ∈ grid.ycuts, (s.im < v ∧ v < t.im) ∨ (t.im < v ∧ v < s.im)

/-- The generated strict grid avoids every internal ledger coordinate. -/
theorem riemannZetaGeneratedStrictGridCuts_avoidsCuts {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im)
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    (RiemannZetaGrid.LedgerAvoidsCuts
      (riemannZetaGeneratedStrictGridCuts z w hre him
        hregular)) := by
  intro s hs
  have havoid :=
    RectangleGeometry.generatedStrictGridCuts_avoidsCuts
      (riemannZetaSingularitiesInRectangle z w) z w hre him
      (fun _ hs ↦
        mem_rectangleOpenBox_of_mem_riemannZetaSingularities
          hregular hs)
      s hs
  exact havoid

/-- The generated strict grid separates every pair of distinct ledger points. -/
theorem riemannZetaGeneratedStrictGridCuts_pairSeparated {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im)
    (hregular :
      RiemannZetaRectangleBoundaryIsRegular z w) :
    (RiemannZetaGrid.LedgerPairsSeparatedByCuts
      (riemannZetaGeneratedStrictGridCuts z w hre him
        hregular)) := by
  intro s hs t ht hne
  exact
    RectangleGeometry.generatedStrictGridCuts_pairsSeparated
      (riemannZetaSingularitiesInRectangle z w) z w hre him
      (fun _ hs ↦
        mem_rectangleOpenBox_of_mem_riemannZetaSingularities
          hregular hs)
      s hs t ht hne

/--
Boundary regularity extends internal-cut avoidance to all endpoint-augmented coordinates.

A catalogued singularity belongs to the outer closed rectangle.  Regularity excludes it from the
boundary, hence places it in the open rectangle and away from all four endpoints.  Combining this
with internal-cut avoidance yields `LedgerAvoidsCoordinates`.
-/
theorem RiemannZetaGrid.ledgerAvoidsCoordinates_of_boundaryRegular {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    (hcuts : (RiemannZetaGrid.LedgerAvoidsCuts grid)) :
    (RiemannZetaGrid.LedgerAvoidsCoordinates grid) := by
  intro s hs
  have hsclosed := (mem_riemannZetaSingularitiesInRectangle_iff.mp hs).1
  have hsopen : s ∈ RectangleGeometry.rectangleOpenBox z w := by
    by_contra hnot
    exact
      not_mem_rectangleClosedBoxBoundary_of_mem_riemannZetaSingularities
        hregular hs
        ⟨hsclosed, by
          simpa only [RectangleGeometry.rectangleOpenBox] using
            hnot⟩
  have hsre : z.re < s.re ∧ s.re < w.re := by
    simpa only [min_eq_left (le_of_lt grid.re_lt), max_eq_right (le_of_lt grid.re_lt),
      Set.mem_preimage, Set.mem_Ioo] using hsopen.1
  have hsim : z.im < s.im ∧ s.im < w.im := by
    simpa only [min_eq_left (le_of_lt grid.im_lt), max_eq_right (le_of_lt grid.im_lt),
      Set.mem_preimage, Set.mem_Ioo] using hsopen.2
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact
    ⟨⟨⟨ne_of_gt hsre.1, (hcuts s hs).1⟩, ne_of_lt hsre.2⟩,
      ⟨⟨ne_of_gt hsim.1, (hcuts s hs).2⟩, ne_of_lt hsim.2⟩⟩

/--
Ledger coordinate avoidance upgrades closed-cell membership to open-cell membership.

`xcoordinates_nodup`, `ycoordinates_nodup`, `cells_nodup`, and `open_disjoint` are inherited
unchanged from the generic `PseudoPrime.AnalyticNumberTheory.RectangleGeometry.StrictGridCuts`
API and are not restated here.
-/
theorem RiemannZetaGrid.point_mem_open_of_avoidsCoordinates {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid :
      (RiemannZetaGrid.LedgerAvoidsCoordinates grid))
    {s : ℂ}
    (hs : s ∈ riemannZetaSingularitiesInRectangle z w)
    {cell : ℂ × ℂ}
    (hcell :
      cell ∈
        (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset)
    (hsclosed : s ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    s ∈ RectangleGeometry.rectangleOpenBox cell.1 cell.2 :=
  RectangleGeometry.StrictGridCuts.point_mem_open_of_avoidsCoordinates
    grid (S := riemannZetaSingularitiesInRectangle z w)
    havoid hs hcell hsclosed

/-- Pair-separating cuts make each strict grid cell contain at most one ledger point. -/
theorem RiemannZetaGrid.cell_point_unique_of_pairSeparated {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid :
      (RiemannZetaGrid.LedgerAvoidsCoordinates grid))
    (hseparated :
      (RiemannZetaGrid.LedgerPairsSeparatedByCuts
        grid))
    (cell : ℂ × ℂ)
    (hcell :
      cell ∈
        (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset)
    (s : ℂ)
    (hs : s ∈ riemannZetaSingularitiesInRectangle z w)
    (hsclosed : s ∈ Rectangle.rectangleClosedBox cell.1 cell.2)
    (t : ℂ)
    (ht : t ∈ riemannZetaSingularitiesInRectangle z w)
    (htclosed : t ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    s = t :=
  RectangleGeometry.StrictGridCuts.cell_point_unique_of_pairSeparated
    grid (S := riemannZetaSingularitiesInRectangle z w)
    havoid hseparated cell hcell hs hsclosed ht htclosed

/-- Every singularity-ledger point is covered by a cell of a strict grid. -/
theorem RiemannZetaGrid.point_covered {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w) (s : ℂ)
    (hs :
      s ∈ riemannZetaSingularitiesInRectangle z w) :
    ∃
      cell ∈
        (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset,
      s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 :=
  RectangleGeometry.StrictGridCuts.point_covered grid
    (mem_riemannZetaSingularitiesInRectangle_iff.mp hs).1

/--
Build interior singularity separation for a strict grid from point-specific geometry.

Strict grid ordering automatically supplies open-cell disjointness.  Callers only prove that each
cell contains at most one ledger point, that ledger points avoid grid edges, and that all ledger
points are covered.  The result feeds directly into the singular-cell assignment constructor.
-/
theorem RiemannZetaGrid.interiorSeparation {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (hunique :
      ∀
        cell ∈
          (RectangleGeometry.rectangleGridCells z w grid.xcuts
              grid.ycuts).toFinset,
        ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
            ∀
              t ∈
                riemannZetaSingularitiesInRectangle z
                  w,
              t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
                s = t)
    (hopen :
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        ∀
          cell ∈
            (RectangleGeometry.rectangleGridCells z w grid.xcuts
                grid.ycuts).toFinset,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
            s ∈ RectangleGeometry.rectangleOpenBox cell.1 cell.2)
    (hcovered :
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        ∃
          cell ∈
            (RectangleGeometry.rectangleGridCells z w grid.xcuts
                grid.ycuts).toFinset,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    RiemannZetaGridInteriorSeparation z w
      (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset := by
  exact
    ⟨hunique, hopen, fun cell hcell other hother hne ↦ grid.open_disjoint hcell hother hne,
      hcovered⟩

/--
Build interior separation when the singularity ledger avoids all strict-grid coordinates.

Coordinate avoidance discharges shared-edge avoidance, while strict ordering supplies open-cell
disjointness.  The only remaining inputs are point separation within each cell and coverage.
-/
theorem RiemannZetaGrid.interiorSeparationOfAvoidsCoordinates {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid :
      (RiemannZetaGrid.LedgerAvoidsCoordinates grid))
    (hunique :
      ∀
        cell ∈
          (RectangleGeometry.rectangleGridCells z w grid.xcuts
              grid.ycuts).toFinset,
        ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
            ∀
              t ∈
                riemannZetaSingularitiesInRectangle z
                  w,
              t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
                s = t)
    (hcovered :
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        ∃
          cell ∈
            (RectangleGeometry.rectangleGridCells z w grid.xcuts
                grid.ycuts).toFinset,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    RiemannZetaGridInteriorSeparation z w
      (RectangleGeometry.rectangleGridCells z w grid.xcuts
          grid.ycuts).toFinset := by
  apply
    (RiemannZetaGrid.interiorSeparation grid) hunique
  · exact fun s hs cell hcell hsclosed ↦
      (RiemannZetaGrid.point_mem_open_of_avoidsCoordinates
          grid)
        havoid hs hcell hsclosed
  · exact hcovered

/--
Build interior separation from boundary regularity and avoidance of internal cut coordinates.

Boundary regularity excludes the four outer endpoints, so callers only certify that the finite
ledger avoids internal cuts.  Point uniqueness inside cells and coverage remain the two genuinely
grid-specific geometric inputs.
-/
theorem RiemannZetaGrid.interiorSeparationOfBoundaryRegular {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (hregular :
      RiemannZetaRectangleBoundaryIsRegular z w)
    (hcuts : (RiemannZetaGrid.LedgerAvoidsCuts grid))
    (hunique :
      ∀
        cell ∈
          (RectangleGeometry.rectangleGridCells z w grid.xcuts
              grid.ycuts).toFinset,
        ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
            ∀
              t ∈
                riemannZetaSingularitiesInRectangle z
                  w,
              t ∈ Rectangle.rectangleClosedBox cell.1 cell.2 →
                s = t)
    (hcovered :
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        ∃
          cell ∈
            (RectangleGeometry.rectangleGridCells z w grid.xcuts
                grid.ycuts).toFinset,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    RiemannZetaGridInteriorSeparation z w
      (RectangleGeometry.rectangleGridCells z w grid.xcuts
          grid.ycuts).toFinset := by
  exact
    (RiemannZetaGrid.interiorSeparationOfAvoidsCoordinates
        grid)
      ((RiemannZetaGrid.ledgerAvoidsCoordinates_of_boundaryRegular
          grid)
        hregular hcuts)
      hunique hcovered

/--
Build interior separation from boundary regularity, cut avoidance, pair separation, and coverage.

The preceding bridges automatically prove shared-edge avoidance, open-cell disjointness, and
cell-level point uniqueness.  Only the finite cut certificates and cell coverage remain explicit.
-/
theorem RiemannZetaGrid.interiorSeparationOfSeparatedCuts {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (hregular :
      RiemannZetaRectangleBoundaryIsRegular z w)
    (hcuts : (RiemannZetaGrid.LedgerAvoidsCuts grid))
    (hseparated :
      (RiemannZetaGrid.LedgerPairsSeparatedByCuts
        grid))
    (hcovered :
      ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
        ∃
          cell ∈
            (RectangleGeometry.rectangleGridCells z w grid.xcuts
                grid.ycuts).toFinset,
          s ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    RiemannZetaGridInteriorSeparation z w
      (RectangleGeometry.rectangleGridCells z w grid.xcuts
          grid.ycuts).toFinset := by
  let havoid :=
    (RiemannZetaGrid.ledgerAvoidsCoordinates_of_boundaryRegular
        grid)
      hregular hcuts
  apply
    (RiemannZetaGrid.interiorSeparationOfBoundaryRegular
        grid)
      hregular hcuts
  · exact
      (RiemannZetaGrid.cell_point_unique_of_pairSeparated
          grid)
        havoid hseparated
  · exact hcovered

/--
Boundary regularity and finite cut certificates produce complete interior grid separation.

Strict-grid interval coverage supplies every ledger point automatically.  Together with cut
avoidance and pair separation, this removes all per-cell geometric inputs from the separation
constructor.
-/
theorem RiemannZetaGrid.interiorSeparationOfCutCertificates {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (hregular :
      RiemannZetaRectangleBoundaryIsRegular z w)
    (hcuts : (RiemannZetaGrid.LedgerAvoidsCuts grid))
    (hseparated :
      (RiemannZetaGrid.LedgerPairsSeparatedByCuts
        grid)) :
    RiemannZetaGridInteriorSeparation z w
      (RectangleGeometry.rectangleGridCells z w grid.xcuts
          grid.ycuts).toFinset := by
  exact
    (RiemannZetaGrid.interiorSeparationOfSeparatedCuts
        grid)
      hregular hcuts hseparated
      (RiemannZetaGrid.point_covered grid)

/--
The generated finite cuts give complete interior separation for a regular ordered rectangle.

Finite avoidance choices, sorting, pair separation, open-cell disjointness, and grid coverage have
all been discharged upstream.  This theorem is the concrete geometry certificate consumed by the
remaining local boundary-deformation layer.
-/
theorem riemannZetaGeneratedGridInteriorSeparation {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hregular :
      RiemannZetaRectangleBoundaryIsRegular z w) :
    let grid :=
      riemannZetaGeneratedStrictGridCuts z w hre him
        hregular
    RiemannZetaGridInteriorSeparation z w
      (RectangleGeometry.rectangleGridCells z w grid.xcuts
          grid.ycuts).toFinset := by
  let grid :=
    riemannZetaGeneratedStrictGridCuts z w hre him
      hregular
  exact
    (RiemannZetaGrid.interiorSeparationOfCutCertificates
        grid)
      hregular
      (riemannZetaGeneratedStrictGridCuts_avoidsCuts
        hre him hregular)
      (riemannZetaGeneratedStrictGridCuts_pairSeparated
        hre him hregular)

/-- Every real cut of a strict grid belongs to the outer unordered interval. -/
theorem RiemannZetaGrid.xcuts_mem_uIcc {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w) {u : ℝ}
    (hu : u ∈ grid.xcuts) : u ∈ Set.uIcc z.re w.re := by
  exact
    Set.mem_uIcc_of_le (le_of_lt (grid.xcuts_inside u hu).1) (le_of_lt (grid.xcuts_inside u hu).2)

/-- Every imaginary cut of a strict grid belongs to the outer unordered interval. -/
theorem RiemannZetaGrid.ycuts_mem_uIcc {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w) {v : ℝ}
    (hv : v ∈ grid.ycuts) : v ∈ Set.uIcc z.im w.im := by
  exact
    Set.mem_uIcc_of_le (le_of_lt (grid.ycuts_inside v hv).1) (le_of_lt (grid.ycuts_inside v hv).2)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
