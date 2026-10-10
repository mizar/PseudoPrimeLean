/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.GridCellShrink

/-!
# Assemble local square residues on a finite rectangle

A finite interior singularity ledger and differentiability elsewhere suffice to build the
avoiding grid, shrink its singular cells, and sum their certified local boundary integrals.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- A function differentiable off a finite rectangle ledger is integrable along every
coordinate segment of a strict grid avoiding that ledger. Coordinate avoidance excludes
singularities; differentiability gives continuity and hence interval integrability. -/
theorem gridCoordinateIntegrable_of_differentiable_off (f : ℂ → ℂ) (S : Finset ℂ) {z w : ℂ}
    (hdiff : ∀ p ∈ Rectangle.rectangleClosedBox z w, p ∉ S → DifferentiableAt ℂ f p)
    (grid : StrictGridCuts z w) (havoid : grid.LedgerAvoidsCoordinates S) :
    RectangleGridCoordinateIntegrable f (z.re :: grid.xcuts ++ [w.re])
      (z.im :: grid.ycuts ++ [w.im]) := by
  have hre (u v : ℝ) : ((u : ℂ) + v * Complex.I).re = u := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have him (u v : ℝ) : ((u : ℂ) + v * Complex.I).im = v := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  constructor
  · intro c hc a ha b hb
    apply intervalIntegrable_horizontal_of_continuousAt
    intro t ht
    apply (hdiff _ ?_ ?_).continuousAt
    · rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, hre, him]
      exact
        ⟨Set.uIcc_subset_uIcc (grid.xcoordinate_mem_uIcc ha) (grid.xcoordinate_mem_uIcc hb) ht,
          grid.ycoordinate_mem_uIcc hc⟩
    · intro hp
      have h := (havoid _ hp).2
      rw [him] at h
      exact h hc
  · intro c hc a ha b hb
    apply intervalIntegrable_vertical_of_continuousAt
    intro t ht
    apply (hdiff _ ?_ ?_).continuousAt
    · rw [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, hre, him]
      exact
        ⟨grid.xcoordinate_mem_uIcc hc,
          Set.uIcc_subset_uIcc (grid.ycoordinate_mem_uIcc ha) (grid.ycoordinate_mem_uIcc hb) ht⟩
    · intro hp
      have h := (havoid _ hp).1
      rw [hre] at h
      exact h hc

/-- For ordered rectangle corners and a finite interior ledger, differentiability off the
ledger and certified local square integrals identify the outer integral with the sum of
local contributions. Construct a separating grid, shrink each singular cell to a certified
square, and cancel regular cells. This applies to shifted kernels without kernel-specific
integrability or cell-assignment hypotheses. -/
theorem rectangleBoundaryIntegral_eq_sum_of_local_residues (f res : ℂ → ℂ) (S : Finset ℂ) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hclosed : ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox z w)
    (hopen : ∀ s ∈ S, s ∈ rectangleOpenBox z w)
    (hdiffGlobal : ∀ p ∈ Rectangle.rectangleClosedBox z w, p ∉ S → DifferentiableAt ℂ f p)
    (hlocal :
      ∀ c ∈ S,
        ∃ R : ℝ,
          0 < R ∧
            ∀ r : ℝ,
              0 < r →
                r ≤ R →
                rectangleBoundaryIntegral f (centeredSquareLower c r) (centeredSquareUpper c r) =
                  res c) :
    rectangleBoundaryIntegral f z w = ∑ s ∈ S, res s := by
  set grid := generatedStrictGridCuts S z w hre him hopen with hgrid_def
  set cells := (rectangleGridCells z w grid.xcuts grid.ycuts).toFinset with hcells_def
  have interior := generatedGridInteriorSeparation S z w hre him hopen hclosed
  set assignment := interior.toAssignment with hassignment_def
  have havoidCuts : grid.LedgerAvoidsCuts S :=
    generatedStrictGridCuts_avoidsCuts S z w hre him hopen
  have havoid : grid.LedgerAvoidsCoordinates S :=
    grid.ledgerAvoidsCoordinates_of_open hopen havoidCuts
  have hcoordint := gridCoordinateIntegrable_of_differentiable_off f S hdiffGlobal grid havoid
  have hgridint : RectangleGridSubdivisionIntegrable f z w grid.xcuts grid.ycuts := by
    apply
      hcoordint.gridSubdivision List.mem_cons_self
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        List.mem_cons_self
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        grid.xcuts grid.ycuts
        (fun c hc ↦ by
          simp only [List.cons_append, List.mem_cons, List.mem_append, hc, List.not_mem_nil,
            or_false, true_or, or_true])
        (fun c hc ↦ by
          simp only [List.cons_append, List.mem_cons, List.mem_append, hc, List.not_mem_nil,
            or_false, true_or, or_true])
  have hsum :
    rectangleBoundaryIntegral f z w =
      ∑ cell ∈ cells, rectangleBoundaryIntegral f cell.1 cell.2 := by
    rw [rectangleBoundaryIntegral_eq_gridSubdivision _ z w grid.xcuts grid.ycuts hgridint,
      rectangleGridSubdivision_eq_sum_toFinset _ z w grid.xcuts grid.ycuts grid.cells_nodup]
  have hxcuts : ∀ u ∈ grid.xcuts, u ∈ Set.uIcc z.re w.re := fun u hu ↦
    Set.mem_uIcc_of_le (grid.xcuts_inside u hu).1.le (grid.xcuts_inside u hu).2.le
  have hycuts : ∀ v ∈ grid.ycuts, v ∈ Set.uIcc z.im w.im := fun v hv ↦
    Set.mem_uIcc_of_le (grid.ycuts_inside v hv).1.le (grid.ycuts_inside v hv).2.le
  have hdiff :
    ∀ cell ∈ cells,
      ∀ y ∈ Rectangle.rectangleClosedBox cell.1 cell.2, y ∉ S → DifferentiableAt ℂ f y := by
    intro cell hcell y hy hyS
    have hcellSubset :=
      rectangleGridCells_closedBox_subset hxcuts hycuts cell
        (by simpa only [hcells_def, List.mem_toFinset] using hcell)
    have hyz : y ∈ Rectangle.rectangleClosedBox z w := hcellSubset hy
    exact hdiffGlobal y hyz hyS
  have hsingular_res :
    ∀ cell ∈ finiteSingularCells S cells,
      rectangleBoundaryIntegral f cell.1 cell.2 = res (assignment.pointOfCell cell) := by
    intro cell hcell
    have hcellmem := mem_singularCells_iff.mp hcell
    have hcellOrder :=
      mem_rectangleGridCells_re_lt_im_lt grid.xcoordinates_pairwise grid.ycoordinates_pairwise
        (by simpa only [hcells_def, List.mem_toFinset] using hcellmem.1)
    set c := assignment.pointOfCell cell with hc_def
    have hpointS : c ∈ S := assignment.point_mem_ledger cell hcell
    obtain ⟨Rc, hRc, hcert⟩ := hlocal c hpointS
    obtain ⟨ε, hε, hball⟩ := interior.exists_closedBall_pointOfCell_subset_open hcell
    set r := min (ε / 2) (Rc / 2) with hr_def
    have hr : 0 < r := lt_min (half_pos hε) (half_pos hRc)
    have hball' : Metric.closedBall c r ⊆ rectangleOpenBox cell.1 cell.2 :=
      (Metric.closedBall_subset_closedBall (le_trans (min_le_left _ _) (half_le_self hε.le))).trans
        hball
    have hcuts := centeredSquare_cuts_inside hcellOrder.1 hcellOrder.2 hr hball'
    set a := centeredSquareLower c r with ha_def
    set b := centeredSquareUpper c r with hb_def
    have hpoint : c ∈ rectangleOpenBox a b := center_mem_centeredSquare_openBox c hr
    have hdiffCell :
      ∀ y ∈ Rectangle.rectangleClosedBox cell.1 cell.2, y ∉ S → DifferentiableAt ℂ f y :=
      hdiff cell hcellmem.1
    have hcopen : c ∈ rectangleOpenBox cell.1 cell.2 := hball' (Metric.mem_closedBall_self hr.le)
    have havoidSq := centeredSquare_augmented_coordinates_avoid hcellOrder.1 hcellOrder.2 hr hcopen
    set xs := cell.1.re :: [a.re, b.re] ++ [cell.2.re] with hxs_def
    set ys := cell.1.im :: [a.im, b.im] ++ [cell.2.im] with hys_def
    have hxmem : ∀ u ∈ xs, u ∈ Set.uIcc cell.1.re cell.2.re := by
      intro u hu
      simp only [hxs_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with (rfl | rfl | rfl) | rfl
      · exact Set.left_mem_uIcc
      · exact Set.mem_uIcc_of_le hcuts.1.le (hcuts.2.1.trans hcuts.2.2.1).le
      · exact Set.mem_uIcc_of_le (hcuts.1.trans hcuts.2.1).le hcuts.2.2.1.le
      · exact Set.right_mem_uIcc
    have hymem : ∀ v ∈ ys, v ∈ Set.uIcc cell.1.im cell.2.im := by
      intro v hv
      simp only [hys_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with (rfl | rfl | rfl) | rfl
      · exact Set.left_mem_uIcc
      · exact Set.mem_uIcc_of_le hcuts.2.2.2.1.le (hcuts.2.2.2.2.1.trans hcuts.2.2.2.2.2).le
      · exact Set.mem_uIcc_of_le (hcuts.2.2.2.1.trans hcuts.2.2.2.2.1).le hcuts.2.2.2.2.2.le
      · exact Set.right_mem_uIcc
    have hcoordint :=
      assignment.kernelCoordinateIntegrable f hcell hdiffCell xs ys hxmem hymem havoidSq.1
        havoidSq.2
    have hgrid3 : RectangleGridSubdivisionIntegrable f cell.1 cell.2 [a.re, b.re] [a.im, b.im] :=
      hcoordint.gridSubdivision
        (by
          simp only [hxs_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, true_or])
        (by
          simp only [hxs_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, or_true])
        (by
          simp only [hys_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, true_or])
        (by
          simp only [hys_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, or_true])
        [a.re, b.re] [a.im, b.im]
        (fun u hu ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;>
            simp only [hxs_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false, true_or, or_true])
        (fun v hv ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;>
            simp only [hys_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false, true_or, or_true])
    have hshrink :=
      assignment.parent_boundaryIntegral_eq_of_shrink f hcell hcuts.1 hcuts.2.1 hcuts.2.2.1
        hcuts.2.2.2.1 hcuts.2.2.2.2.1 hcuts.2.2.2.2.2 hpoint hdiffCell hgrid3
    rw [hshrink]
    have hrRc : r ≤ Rc := le_trans (min_le_right _ _) (half_le_self hRc.le)
    exact hcert r hr hrRc
  exact
    rectangleBoundaryIntegral_eq_sum_res f (fun s ↦ res s) S cells z w assignment hsum hdiff
      hsingular_res

/-- On an ordered rectangle with an interior simple pole, an analytic local
regularization and differentiability elsewhere determine the boundary integral
as 2*pi*i times the regularization at the pole. Use the local square certificate
and assemble it with the singleton singularity ledger. This avoids an external
simple-pole residue theorem when shifting Mellin contours. -/
theorem rectangleBoundaryIntegral_eq_of_simple_regularization {f h : ℂ → ℂ} {z w c : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hc : c ∈ rectangleOpenBox z w)
    (hd : ∀ p ∈ Rectangle.rectangleClosedBox z w, p ≠ c → DifferentiableAt ℂ f p)
    (hh : AnalyticAt ℂ h c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun s ↦ (s - c) * f s) h) :
    rectangleBoundaryIntegral f z w = 2 * Real.pi * Complex.I * h c := by
  classical
  have hl := exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul hh heq
  have hb :=
    rectangleBoundaryIntegral_eq_sum_of_local_residues f (fun _ ↦ 2 * Real.pi * Complex.I * h c) {c}
      hre him
      (fun s hs ↦ by
        rw [Finset.mem_singleton] at hs
        subst s
        exact rectangleOpenBox_subset_rectangleClosedBox z w hc)
      (fun s hs ↦ by
        rw [Finset.mem_singleton] at hs; exact hs ▸ hc)
      (fun p hp hn ↦
        hd p hp
          (by
            intro he
            exact hn (Finset.mem_singleton.mpr he)))
      (fun s hs ↦ by
        rw [Finset.mem_singleton] at hs; exact hs ▸ hl)
  simpa only [Finset.sum_singleton] using hb

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry
