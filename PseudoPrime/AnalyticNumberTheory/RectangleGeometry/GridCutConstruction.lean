/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.ResidueTheorem

/-!
# Generic strict-grid cut construction for a finite singularity set

This file constructs strict-grid cuts over an arbitrary finite singularity
set `S : Finset ℂ`, producing a `RectangleGeometry.GridInteriorSeparation S cells`
ready to feed `RectangleGeometry.GridInteriorSeparation.toAssignment` and ultimately
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_sum_res`.

`RectangleGeometry.StrictGridCuts` itself and its `cells_nodup`/`open_disjoint` consequences
mention no singularity
set at all; only the cut-generation
functions and the final separation certificates are parametrized by `S` here.
-/

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/--
Ordered finite cut coordinates for a rectangular contour grid. `xcuts`/`ycuts` are the internal
real/imaginary cut coordinates; the `pairwise` fields make each list strictly increasing, and the
`inside` fields place every cut strictly between the outer rectangle's endpoints.
-/
structure StrictGridCuts (z w : ℂ) where
  xcuts : List ℝ
  ycuts : List ℝ
  re_lt : z.re < w.re
  im_lt : z.im < w.im
  xcuts_pairwise : xcuts.Pairwise (· < ·)
  ycuts_pairwise : ycuts.Pairwise (· < ·)
  xcuts_inside : ∀ u ∈ xcuts, z.re < u ∧ u < w.re
  ycuts_inside : ∀ v ∈ ycuts, z.im < v ∧ v < w.im

/-- The endpoint-augmented real coordinates of a strict grid remain strictly increasing. -/
theorem StrictGridCuts.xcoordinates_pairwise {z w : ℂ}
    (grid : StrictGridCuts z w) :
    (z.re :: grid.xcuts ++ [w.re]).Pairwise (· < ·) :=
  endpointAugmentedCoordinates_pairwise
    grid.re_lt grid.xcuts_pairwise grid.xcuts_inside

/-- The endpoint-augmented imaginary coordinates of a strict grid remain strictly increasing. -/
theorem StrictGridCuts.ycoordinates_pairwise {z w : ℂ}
    (grid : StrictGridCuts z w) :
    (z.im :: grid.ycuts ++ [w.im]).Pairwise (· < ·) :=
  endpointAugmentedCoordinates_pairwise
    grid.im_lt grid.ycuts_pairwise grid.ycuts_inside

/-- The endpoint-augmented real coordinates of a strict grid are duplicate-free. -/
theorem StrictGridCuts.xcoordinates_nodup {z w : ℂ}
    (grid : StrictGridCuts z w) :
    (z.re :: grid.xcuts ++ [w.re]).Nodup :=
  endpointAugmentedCoordinates_nodup grid.re_lt
    grid.xcuts_pairwise grid.xcuts_inside

/-- The endpoint-augmented imaginary coordinates of a strict grid are duplicate-free. -/
theorem StrictGridCuts.ycoordinates_nodup {z w : ℂ}
    (grid : StrictGridCuts z w) :
    (z.im :: grid.ycuts ++ [w.im]).Nodup :=
  endpointAugmentedCoordinates_nodup grid.im_lt
    grid.ycuts_pairwise grid.ycuts_inside

/-- Every endpoint-augmented real grid coordinate lies in the outer unordered interval. -/
theorem StrictGridCuts.xcoordinate_mem_uIcc {z w : ℂ}
    (grid : StrictGridCuts z w) {c : ℝ}
    (hc : c ∈ z.re :: grid.xcuts ++ [w.re]) : c ∈ Set.uIcc z.re w.re := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · exact Set.left_mem_uIcc
  · rw [Set.uIcc_of_lt grid.re_lt]
    exact ⟨le_of_lt (grid.xcuts_inside c hc).1, le_of_lt (grid.xcuts_inside c hc).2⟩
  · exact Set.right_mem_uIcc

/-- Every endpoint-augmented imaginary grid coordinate lies in the outer unordered interval. -/
theorem StrictGridCuts.ycoordinate_mem_uIcc {z w : ℂ}
    (grid : StrictGridCuts z w) {c : ℝ}
    (hc : c ∈ z.im :: grid.ycuts ++ [w.im]) : c ∈ Set.uIcc z.im w.im := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · exact Set.left_mem_uIcc
  · rw [Set.uIcc_of_lt grid.im_lt]
    exact ⟨le_of_lt (grid.ycuts_inside c hc).1, le_of_lt (grid.ycuts_inside c hc).2⟩
  · exact Set.right_mem_uIcc

/-- The rectangular cell list induced by a strict grid is duplicate-free. -/
theorem StrictGridCuts.cells_nodup {z w : ℂ}
    (grid : StrictGridCuts z w) :
    (rectangleGridCells z w grid.xcuts
        grid.ycuts).Nodup :=
  rectangleGridCells_nodup
    grid.xcoordinates_nodup grid.ycoordinates_nodup

/-- Distinct cells of a strict grid have disjoint open rectangles. -/
theorem StrictGridCuts.open_disjoint {z w : ℂ}
    (grid : StrictGridCuts z w)
    {cell other : ℂ × ℂ}
    (hcell :
      cell ∈
        (rectangleGridCells z w grid.xcuts
            grid.ycuts).toFinset)
    (hother :
      other ∈
        (rectangleGridCells z w grid.xcuts
            grid.ycuts).toFinset)
    (hne : cell ≠ other) :
    Disjoint (rectangleOpenBox cell.1 cell.2)
      (rectangleOpenBox other.1 other.2) :=
  rectangleGridCells_openBox_disjoint
    grid.xcoordinates_pairwise grid.ycoordinates_pairwise
    (by simpa only [List.mem_toFinset] using hcell) (by simpa only [List.mem_toFinset] using hother)
    hne

/-- The outer singularity set `S` avoids every endpoint-augmented grid coordinate. -/
def StrictGridCuts.LedgerAvoidsCoordinates {z w : ℂ}
    (grid : StrictGridCuts z w) (S : Finset ℂ) :
    Prop :=
  ∀ s ∈ S, s.re ∉ z.re :: grid.xcuts ++ [w.re] ∧ s.im ∉ z.im :: grid.ycuts ++ [w.im]

/-- The outer singularity set `S` avoids every internal cut coordinate of a strict grid. -/
def StrictGridCuts.LedgerAvoidsCuts {z w : ℂ}
    (grid : StrictGridCuts z w) (S : Finset ℂ) :
    Prop :=
  ∀ s ∈ S, s.re ∉ grid.xcuts ∧ s.im ∉ grid.ycuts

/--
Internal cuts separate every pair of distinct points of `S` in some coordinate: for each ordered
pair of distinct points, a real or imaginary cut lies strictly between their corresponding
coordinates in either orientation.
-/
def StrictGridCuts.LedgerPairsSeparatedByCuts {z w : ℂ}
    (grid : StrictGridCuts z w) (S : Finset ℂ) :
    Prop :=
  ∀ s ∈ S,
    ∀ t ∈ S,
      s ≠ t →
        (∃ u ∈ grid.xcuts, (s.re < u ∧ u < t.re) ∨ (t.re < u ∧ u < s.re)) ∨
          ∃ v ∈ grid.ycuts, (s.im < v ∧ v < t.im) ∨ (t.im < v ∧ v < s.im)

/-- Interior containment and avoidance of internal cuts imply avoidance of all grid coordinates,
including the outer endpoints. -/
theorem StrictGridCuts.ledgerAvoidsCoordinates_of_open {z w : ℂ}
    (grid : StrictGridCuts z w) {S : Finset ℂ}
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w)
    (hcuts : grid.LedgerAvoidsCuts S) : grid.LedgerAvoidsCoordinates S := by
  intro s hs
  have hsre : z.re < s.re ∧ s.re < w.re := by
    simpa only [min_eq_left (le_of_lt grid.re_lt), max_eq_right (le_of_lt grid.re_lt),
      Set.mem_preimage, Set.mem_Ioo] using (hopen s hs).1
  have hsim : z.im < s.im ∧ s.im < w.im := by
    simpa only [min_eq_left (le_of_lt grid.im_lt), max_eq_right (le_of_lt grid.im_lt),
      Set.mem_preimage, Set.mem_Ioo] using (hopen s hs).2
  refine ⟨?_, ?_⟩
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact hsre.1.ne' heq
    rcases List.mem_append.mp hmem' with hxcuts | hlast
    · exact (hcuts s hs).1 hxcuts
    · exact hsre.2.ne (List.mem_singleton.mp hlast)
  · intro hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · exact hsim.1.ne' heq
    rcases List.mem_append.mp hmem' with hycuts | hlast
    · exact (hcuts s hs).2 hycuts
    · exact hsim.2.ne (List.mem_singleton.mp hlast)

/-- Ledger coordinate avoidance upgrades closed-cell membership to open-cell membership. -/
theorem StrictGridCuts.point_mem_open_of_avoidsCoordinates {z w : ℂ}
    (grid : StrictGridCuts z w) {S : Finset ℂ}
    (havoid : grid.LedgerAvoidsCoordinates S) {s : ℂ} (hs : s ∈ S) {cell : ℂ × ℂ}
    (hcell :
      cell ∈
        (rectangleGridCells z w grid.xcuts
            grid.ycuts).toFinset)
    (hsclosed : s ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    s ∈ rectangleOpenBox cell.1 cell.2 :=
  mem_rectangleGridCell_openBox_of_avoids_coordinates
    grid.xcoordinates_pairwise grid.ycoordinates_pairwise
    (by simpa only [List.mem_toFinset] using hcell) hsclosed (havoid s hs).1 (havoid s hs).2

/-- Pair-separating cuts make each strict grid cell contain at most one point of `S`. -/
theorem StrictGridCuts.cell_point_unique_of_pairSeparated {z w : ℂ}
    (grid : StrictGridCuts z w) {S : Finset ℂ}
    (havoid : grid.LedgerAvoidsCoordinates S) (hseparated : grid.LedgerPairsSeparatedByCuts S)
    (cell : ℂ × ℂ)
    (hcell :
      cell ∈
        (rectangleGridCells z w grid.xcuts
            grid.ycuts).toFinset)
    {s : ℂ} (hs : s ∈ S)
    (hsclosed : s ∈ Rectangle.rectangleClosedBox cell.1 cell.2)
    {t : ℂ} (ht : t ∈ S)
    (htclosed : t ∈ Rectangle.rectangleClosedBox cell.1 cell.2) :
    s = t := by
  by_contra hne
  have hsopen := grid.point_mem_open_of_avoidsCoordinates havoid hs hcell hsclosed
  have htopen := grid.point_mem_open_of_avoidsCoordinates havoid ht hcell htclosed
  apply hne
  apply
    eq_of_mem_same_gridCell_openBox_of_coordinateSeparated
      grid.xcoordinates_pairwise grid.ycoordinates_pairwise
      (by simpa only [List.mem_toFinset] using hcell) hsopen htopen
  rcases hseparated s hs t ht hne with ⟨u, hu, hbetween⟩ | ⟨v, hv, hbetween⟩
  · exact
      Or.inl
        ⟨u, by
          simp only [List.cons_append, List.mem_cons, List.mem_append, hu, List.not_mem_nil,
            or_false, true_or, or_true],
          hbetween⟩
  · exact
      Or.inr
        ⟨v, by
          simp only [List.cons_append, List.mem_cons, List.mem_append, hv, List.not_mem_nil,
            or_false, true_or, or_true],
          hbetween⟩

/-- Every point of a closed rectangle is covered by a cell of a strict grid on it. -/
theorem StrictGridCuts.point_covered {z w : ℂ}
    (grid : StrictGridCuts z w) {s : ℂ}
    (hs : s ∈ Rectangle.rectangleClosedBox z w) :
    ∃
      cell ∈
        (rectangleGridCells z w grid.xcuts
            grid.ycuts).toFinset,
      s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 := by
  obtain ⟨cell, hcell, hscell⟩ :=
    exists_mem_rectangleGridCell_closedBox
      grid.re_lt grid.im_lt grid.xcuts_pairwise grid.ycuts_pairwise grid.xcuts_inside
      grid.ycuts_inside hs
  exact ⟨cell, by simpa only [List.mem_toFinset] using hcell, hscell⟩

/-- A strict grid with cut-avoidance and pair-separation certificates for `S` (relative to an
outer rectangle whose interior contains `S`) gives complete interior singularity separation. -/
theorem StrictGridCuts.interiorSeparationOfCutCertificates {z w : ℂ}
    (grid : StrictGridCuts z w) {S : Finset ℂ}
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w)
    (hclosed : ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox z w)
    (hcuts : grid.LedgerAvoidsCuts S) (hseparated : grid.LedgerPairsSeparatedByCuts S) :
    GridInteriorSeparation S
      (rectangleGridCells z w grid.xcuts
          grid.ycuts).toFinset := by
  have havoid := grid.ledgerAvoidsCoordinates_of_open hopen hcuts
  exact
    { cell_point_unique := fun cell hcell s hs hsclosed t ht htclosed =>
        grid.cell_point_unique_of_pairSeparated havoid hseparated cell hcell hs hsclosed ht htclosed
      point_mem_open := fun s hs cell hcell hsclosed =>
        grid.point_mem_open_of_avoidsCoordinates havoid hs hcell hsclosed
      open_disjoint := fun cell hcell other hother hne => grid.open_disjoint hcell hother hne
      point_covered := fun s hs => grid.point_covered (hclosed s hs) }

/-- The real coordinates occurring in `S`. -/
noncomputable def singularityRealCoordinates (S : Finset ℂ) : Finset ℝ :=
  S.image Complex.re

/-- The imaginary coordinates occurring in `S`. -/
noncomputable def singularityImagCoordinates (S : Finset ℂ) : Finset ℝ :=
  S.image Complex.im

/-- Ordered point pairs of `S` whose real coordinates are strictly increasing. -/
noncomputable def orderedRealPairs (S : Finset ℂ) : Finset (ℂ × ℂ) :=
  (S ×ˢ S).filter fun p ↦ p.1.re < p.2.re

/-- Ordered point pairs of `S` whose imaginary coordinates are strictly increasing. -/
noncomputable def orderedImagPairs (S : Finset ℂ) : Finset (ℂ × ℂ) :=
  (S ×ˢ S).filter fun p ↦ p.1.im < p.2.im

/-- One coordinate-avoiding real cut candidate for every real-separated pair of `S`. -/
noncomputable def realCutCandidates (S : Finset ℂ) : Finset ℝ :=
  (orderedRealPairs S).image fun p ↦
    avoidingCut
      (singularityRealCoordinates S) p.1.re
      p.2.re

/-- One coordinate-avoiding imaginary cut candidate for every imaginary-separated pair of `S`. -/
noncomputable def imagCutCandidates (S : Finset ℂ) : Finset ℝ :=
  (orderedImagPairs S).image fun p ↦
    avoidingCut
      (singularityImagCoordinates S) p.1.im
      p.2.im

/-- The real cut candidates of `S`, sorted into a strictly increasing list. -/
noncomputable def realCuts (S : Finset ℂ) : List ℝ :=
  (realCutCandidates S).sort

/-- The imaginary cut candidates of `S`, sorted into a strictly increasing list. -/
noncomputable def imagCuts (S : Finset ℂ) : List ℝ :=
  (imagCutCandidates S).sort

/-- The sorted real cut list of `S` is strictly increasing. -/
theorem realCuts_pairwise (S : Finset ℂ) :
    (realCuts S).Pairwise (· < ·) :=
  (Finset.sortedLT_sort
      (realCutCandidates S)).pairwise

/-- The sorted imaginary cut list of `S` is strictly increasing. -/
theorem imagCuts_pairwise (S : Finset ℂ) :
    (imagCuts S).Pairwise (· < ·) :=
  (Finset.sortedLT_sort
      (imagCutCandidates S)).pairwise

/-- Every generated real cut of `S` avoids every real coordinate of `S`. -/
theorem realCuts_avoid {S : Finset ℂ} {u : ℝ}
    (hu : u ∈ realCuts S) {s : ℂ} (hs : s ∈ S) :
    u ≠ s.re := by
  classical
  rw [realCuts, Finset.mem_sort] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
  have hp' := Finset.mem_filter.mp hp
  have havoid :=
    (avoidingCut_spec
        (singularityRealCoordinates S) hp'.2).2.2
  intro heq
  exact havoid (heq ▸ Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- Every generated imaginary cut of `S` avoids every imaginary coordinate of `S`. -/
theorem imagCuts_avoid {S : Finset ℂ} {v : ℝ}
    (hv : v ∈ imagCuts S) {s : ℂ} (hs : s ∈ S) :
    v ≠ s.im := by
  classical
  rw [imagCuts, Finset.mem_sort] at hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hp' := Finset.mem_filter.mp hp
  have havoid :=
    (avoidingCut_spec
        (singularityImagCoordinates S) hp'.2).2.2
  intro heq
  exact havoid (heq ▸ Finset.mem_image.mpr ⟨s, hs, rfl⟩)

/-- Generated real and imaginary cuts separate every pair of distinct points of `S`. -/
theorem generatedCuts_pair_separated {S : Finset ℂ} {s t : ℂ} (hs : s ∈ S) (ht : t ∈ S)
    (hne : s ≠ t) :
    (∃ u ∈ realCuts S,
        (s.re < u ∧ u < t.re) ∨ (t.re < u ∧ u < s.re)) ∨
      ∃ v ∈ imagCuts S,
        (s.im < v ∧ v < t.im) ∨ (t.im < v ∧ v < s.im) := by
  classical
  by_cases hre : s.re = t.re
  · have him : s.im ≠ t.im := fun him ↦ hne (Complex.ext hre him)
    rcases lt_or_gt_of_ne him with hst | hts
    · refine
        Or.inr
          ⟨avoidingCut
              (singularityImagCoordinates S) s.im
              t.im,
            ?_,
            Or.inl
              ⟨(avoidingCut_spec _ hst).1,
                (avoidingCut_spec _ hst).2.1⟩⟩
      rw [imagCuts, Finset.mem_sort,
        imagCutCandidates]
      exact
        Finset.mem_image.mpr
          ⟨(s, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, ht⟩, hst⟩, rfl⟩
    · refine
        Or.inr
          ⟨avoidingCut
              (singularityImagCoordinates S) t.im
              s.im,
            ?_,
            Or.inr
              ⟨(avoidingCut_spec _ hts).1,
                (avoidingCut_spec _ hts).2.1⟩⟩
      rw [imagCuts, Finset.mem_sort,
        imagCutCandidates]
      exact
        Finset.mem_image.mpr
          ⟨(t, s), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, hs⟩, hts⟩, rfl⟩
  · rcases lt_or_gt_of_ne hre with hst | hts
    · refine
        Or.inl
          ⟨avoidingCut
              (singularityRealCoordinates S) s.re
              t.re,
            ?_,
            Or.inl
              ⟨(avoidingCut_spec _ hst).1,
                (avoidingCut_spec _ hst).2.1⟩⟩
      rw [realCuts, Finset.mem_sort,
        realCutCandidates]
      exact
        Finset.mem_image.mpr
          ⟨(s, t), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs, ht⟩, hst⟩, rfl⟩
    · refine
        Or.inl
          ⟨avoidingCut
              (singularityRealCoordinates S) t.re
              s.re,
            ?_,
            Or.inr
              ⟨(avoidingCut_spec _ hts).1,
                (avoidingCut_spec _ hts).2.1⟩⟩
      rw [realCuts, Finset.mem_sort,
        realCutCandidates]
      exact
        Finset.mem_image.mpr
          ⟨(t, s), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht, hs⟩, hts⟩, rfl⟩

/-- Under interior containment, every generated real cut of `S` lies inside the outer interval. -/
theorem realCuts_inside {S : Finset ℂ} {z w : ℂ} (hre : z.re < w.re)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w)
    {u : ℝ} (hu : u ∈ realCuts S) :
    z.re < u ∧ u < w.re := by
  classical
  rw [realCuts, Finset.mem_sort,
    realCutCandidates] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
  have hp' := Finset.mem_filter.mp hp
  have hpMem := Finset.mem_product.mp hp'.1
  have hopenLeft := hopen p.1 hpMem.1
  have hopenRight := hopen p.2 hpMem.2
  have hleft : z.re < p.1.re := by simpa only [min_eq_left (le_of_lt hre)] using hopenLeft.1.1
  have hright : p.2.re < w.re := by simpa only [max_eq_right (le_of_lt hre)] using hopenRight.1.2
  have hcut :=
    avoidingCut_spec
      (singularityRealCoordinates S) hp'.2
  exact ⟨hleft.trans hcut.1, hcut.2.1.trans hright⟩

/-- Under interior containment, every generated imaginary cut of `S` lies inside the outer
interval. -/
theorem imagCuts_inside {S : Finset ℂ} {z w : ℂ} (him : z.im < w.im)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w)
    {v : ℝ} (hv : v ∈ imagCuts S) :
    z.im < v ∧ v < w.im := by
  classical
  rw [imagCuts, Finset.mem_sort,
    imagCutCandidates] at hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  have hp' := Finset.mem_filter.mp hp
  have hpMem := Finset.mem_product.mp hp'.1
  have hopenLeft := hopen p.1 hpMem.1
  have hopenRight := hopen p.2 hpMem.2
  have hleft : z.im < p.1.im := by simpa only [min_eq_left (le_of_lt him)] using hopenLeft.2.1
  have hright : p.2.im < w.im := by simpa only [max_eq_right (le_of_lt him)] using hopenRight.2.2
  have hcut :=
    avoidingCut_spec
      (singularityImagCoordinates S) hp'.2
  exact ⟨hleft.trans hcut.1, hcut.2.1.trans hright⟩

/-- The strict grid generated from `S`'s own coordinates. -/
noncomputable def generatedStrictGridCuts (S : Finset ℂ) (z w : ℂ) (hre : z.re < w.re)
    (him : z.im < w.im)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w) :
    StrictGridCuts z w
    where
  xcuts := realCuts S
  ycuts := imagCuts S
  re_lt := hre
  im_lt := him
  xcuts_pairwise := realCuts_pairwise S
  ycuts_pairwise := imagCuts_pairwise S
  xcuts_inside := fun _ hu ↦
    realCuts_inside hre hopen hu
  ycuts_inside := fun _ hv ↦
    imagCuts_inside him hopen hv

/-- The generated strict grid avoids every internal coordinate of `S`. -/
theorem generatedStrictGridCuts_avoidsCuts (S : Finset ℂ) (z w : ℂ) (hre : z.re < w.re)
    (him : z.im < w.im)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w) :
    (generatedStrictGridCuts S z w hre him
          hopen).LedgerAvoidsCuts
      S := by
  intro s hs
  exact
    ⟨fun hu ↦ (realCuts_avoid hu hs) rfl,
      fun hv ↦ (imagCuts_avoid hv hs) rfl⟩

/-- The generated strict grid separates every pair of distinct points of `S`. -/
theorem generatedStrictGridCuts_pairsSeparated (S : Finset ℂ) (z w : ℂ) (hre : z.re < w.re)
    (him : z.im < w.im)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w) :
    (generatedStrictGridCuts S z w hre him
          hopen).LedgerPairsSeparatedByCuts
      S :=
  fun _ hs _ ht hne ↦
  generatedCuts_pair_separated hs ht hne

/-- The generated grid interior separation certificate for `S`, built from `S`'s own geometry. -/
theorem generatedGridInteriorSeparation (S : Finset ℂ) (z w : ℂ) (hre : z.re < w.re)
    (him : z.im < w.im)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w)
    (hclosed : ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox z w) :
    GridInteriorSeparation S
      (rectangleGridCells z w
          (generatedStrictGridCuts S z w hre him
              hopen).xcuts
          (generatedStrictGridCuts S z w hre him
              hopen).ycuts).toFinset :=
  (generatedStrictGridCuts S z w hre him
        hopen).interiorSeparationOfCutCertificates
    hopen hclosed
    (generatedStrictGridCuts_avoidsCuts S z w hre
      him hopen)
    (generatedStrictGridCuts_pairsSeparated S z w
      hre him hopen)

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry
