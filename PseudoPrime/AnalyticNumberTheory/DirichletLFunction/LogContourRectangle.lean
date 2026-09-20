/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveContourRectangle
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogResidueLedger

/-! General smoothed-contour identities and bounds. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `x > 0`, a nontrivial character, and an `L`-zero `ρ ≠ 0`.
Conclusion: some centered square has logarithmic boundary integral equal to `2πi` times that
zero's designated contribution.
Content: feed the local analytic regularization and scaled-kernel equality to the shared rectangle
simple-pole theorem.
Role: this is the local logarithmic residue certificate consumed by punctured-grid bookkeeping.
-/
theorem exists_dirichletRectangleBoundaryIntegral_log_eq_two_pi_I_mul_zeroContribution {N : ℕ}
    [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
            (RectangleGeometry.centeredSquareLower ρ R)
            (RectangleGeometry.centeredSquareUpper ρ R) =
          2 * Real.pi * Complex.I *
            (-(dirichletLFunctionZeroMultiplicity χ ρ : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2) := by
  obtain ⟨g, -, hganalytic, hgzero, heq⟩ :=
    exists_eventuallyEq_logKernel_dirichletLFunctionZeroRegularization x hχ hρ0 hzero
  have hh :
    AnalyticAt ℂ (dirichletLogZeroRegularization x ρ (dirichletLFunctionZeroMultiplicity χ ρ) g)
      ρ :=
    analyticAt_dirichletLogZeroRegularization hx hρ0 _ hganalytic hgzero
  obtain ⟨R, hR, hRes⟩ := RectangleGeometry.exists_rectangleBoundaryIntegral_eq_two_pi_I_mul hh heq
  refine ⟨R, hR, ?_⟩
  simpa only [RectangleGeometry.rectangleBoundaryIntegral, smul_eq_mul, neg_mul] using
    (hRes.trans
      (by
        rw [dirichletLogZeroRegularization_self]
        ring))

/--
Coordinate avoidance makes the primitive logarithmic kernel integrable on every
finite outer grid-coordinate segment. Mirrors
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalKernelCoordinateIntegrable`
exactly, taking the `.2` component of the
already-bundled horizontal/vertical integrability facts instead of the `.1` component.
-/
theorem dirichletLogKernelCoordinateIntegrable {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid : grid.LedgerAvoidsCoordinates (dirichletLFunctionSingularitiesInRectangle χ hne z w)) :
    RectangleGeometry.RectangleGridCoordinateIntegrable (dirichletLogContourKernel x χ)
      (z.re :: grid.xcuts ++ [w.re]) (z.im :: grid.ycuts ++ [w.im]) := by
  constructor
  · intro c hc a ha b hb
    exact
      (intervalIntegrable_dirichletKernels_horizontal hx hne (grid.xcoordinate_mem_uIcc ha)
          (grid.xcoordinate_mem_uIcc hb) (grid.ycoordinate_mem_uIcc hc) fun s hs hsc ↦
          (havoid s hs).2 (hsc ▸ hc)).2
  · intro c hc a ha b hb
    exact
      (intervalIntegrable_dirichletKernels_vertical hx hne (grid.xcoordinate_mem_uIcc hc)
          (grid.ycoordinate_mem_uIcc ha) (grid.ycoordinate_mem_uIcc hb) fun s hs hsc ↦
          (havoid s hs).1 (hsc ▸ hc)).2

/--
The primitive logarithmic finite contour identity. For an outer rectangle whose
primitive singularity ledger stays in its interior, the log-kernel boundary integral is `2πi`
times the sum of `PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogResidueAt` over
that ledger. Mirrors
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletReciprocalFiniteContourIdentity`
line-for-line, replacing every kernel/residue/
coordinate-integrability name with its log-kernel counterpart.
-/
theorem dirichletLogFiniteContourIdentity {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hopen :
      ∀ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ) z w =
      ∑ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
        2 * Real.pi * Complex.I * dirichletLogResidueAt hne x s := by
  set S := dirichletLFunctionSingularitiesInRectangle χ hne z w with hS_def
  have hclosed : ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox z w := fun s hs ↦
    (mem_dirichletLFunctionSingularitiesInRectangle_iff.mp hs).1
  set grid := RectangleGeometry.generatedStrictGridCuts S z w hre him hopen with hgrid_def
  set cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset with
    hcells_def
  have interior := RectangleGeometry.generatedGridInteriorSeparation S z w hre him hopen hclosed
  set assignment := interior.toAssignment with hassignment_def
  have havoidCuts : grid.LedgerAvoidsCuts S :=
    RectangleGeometry.generatedStrictGridCuts_avoidsCuts S z w hre him hopen
  have havoid : grid.LedgerAvoidsCoordinates S :=
    grid.ledgerAvoidsCoordinates_of_open hopen havoidCuts
  have hcoordint := dirichletLogKernelCoordinateIntegrable hx hne grid havoid
  have hgridint :
    RectangleGeometry.RectangleGridSubdivisionIntegrable (dirichletLogContourKernel x χ) z w
      grid.xcuts grid.ycuts := by
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
    RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ) z w =
      ∑ cell ∈ cells,
        RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ) cell.1
          cell.2 := by
    rw [RectangleGeometry.rectangleBoundaryIntegral_eq_gridSubdivision _ z w grid.xcuts grid.ycuts
        hgridint,
      RectangleGeometry.rectangleGridSubdivision_eq_sum_toFinset _ z w grid.xcuts grid.ycuts
        grid.cells_nodup]
  have hxcuts : ∀ u ∈ grid.xcuts, u ∈ Set.uIcc z.re w.re := fun u hu ↦
    Set.mem_uIcc_of_le (grid.xcuts_inside u hu).1.le (grid.xcuts_inside u hu).2.le
  have hycuts : ∀ v ∈ grid.ycuts, v ∈ Set.uIcc z.im w.im := fun v hv ↦
    Set.mem_uIcc_of_le (grid.ycuts_inside v hv).1.le (grid.ycuts_inside v hv).2.le
  have hdiff :
    ∀ cell ∈ cells,
      ∀ y ∈ Rectangle.rectangleClosedBox cell.1 cell.2,
        y ∉ S → DifferentiableAt ℂ (dirichletLogContourKernel x χ) y := by
    intro cell hcell y hy hyS
    have hcellSubset :=
      RectangleGeometry.rectangleGridCells_closedBox_subset hxcuts hycuts cell
        (by simpa only [hcells_def, List.mem_toFinset] using hcell)
    have hyz : y ∈ Rectangle.rectangleClosedBox z w := hcellSubset hy
    have hy' : ¬(y = 0 ∨ y = 1 ∨ DirichletCharacter.LFunction χ y = 0) := fun hmem ↦
      hyS (mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr ⟨hyz, hmem⟩)
    push Not at hy'
    exact differentiableAt_dirichletLogContourKernel hx hne hy'.1 hy'.2.2
  have hsingular_res :
    ∀ cell ∈ RectangleGeometry.finiteSingularCells S cells,
      RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ) cell.1 cell.2 =
        2 * Real.pi * Complex.I * dirichletLogResidueAt hne x (assignment.pointOfCell cell) := by
    intro cell hcell
    have hcellmem := RectangleGeometry.mem_singularCells_iff.mp hcell
    have hcellOrder :=
      RectangleGeometry.mem_rectangleGridCells_re_lt_im_lt grid.xcoordinates_pairwise
        grid.ycoordinates_pairwise (by simpa only [hcells_def, List.mem_toFinset] using hcellmem.1)
    set c := assignment.pointOfCell cell with hc_def
    have hpointS : c ∈ S := assignment.point_mem_ledger cell hcell
    have hpointHyp := (mem_dirichletLFunctionSingularitiesInRectangle_iff.mp hpointS).2
    obtain ⟨Rc, hRc, hcert⟩ :=
      exists_radius_forall_dirichletRectangleBoundaryIntegral_log_residueAt hx hprimitive hne
        hpointHyp
    obtain ⟨ε, hε, hball⟩ := interior.exists_closedBall_pointOfCell_subset_open hcell
    set r := min (ε / 2) (Rc / 2) with hr_def
    have hr : 0 < r := lt_min (by linarith) (by linarith)
    have hball' : Metric.closedBall c r ⊆ RectangleGeometry.rectangleOpenBox cell.1 cell.2 :=
      (Metric.closedBall_subset_closedBall
            (le_trans (min_le_left _ _) (by linarith : ε / 2 ≤ ε))).trans
        hball
    have hcuts := RectangleGeometry.centeredSquare_cuts_inside hcellOrder.1 hcellOrder.2 hr hball'
    set a := RectangleGeometry.centeredSquareLower c r with ha_def
    set b := RectangleGeometry.centeredSquareUpper c r with hb_def
    have hpoint : c ∈ RectangleGeometry.rectangleOpenBox a b :=
      RectangleGeometry.center_mem_centeredSquare_openBox c hr
    have hdiffCell :
      ∀ y ∈ Rectangle.rectangleClosedBox cell.1 cell.2,
        y ∉ S → DifferentiableAt ℂ (dirichletLogContourKernel x χ) y :=
      hdiff cell hcellmem.1
    have hcopen : c ∈ RectangleGeometry.rectangleOpenBox cell.1 cell.2 :=
      hball' (Metric.mem_closedBall_self hr.le)
    have havoidSq :=
      RectangleGeometry.centeredSquare_augmented_coordinates_avoid hcellOrder.1 hcellOrder.2 hr
        hcopen
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
      assignment.kernelCoordinateIntegrable (dirichletLogContourKernel x χ) hcell hdiffCell xs ys
        hxmem hymem havoidSq.1 havoidSq.2
    have hgrid3 :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (dirichletLogContourKernel x χ) cell.1
        cell.2 [a.re, b.re] [a.im, b.im] :=
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
      assignment.parent_boundaryIntegral_eq_of_shrink (dirichletLogContourKernel x χ) hcell hcuts.1
        hcuts.2.1 hcuts.2.2.1 hcuts.2.2.2.1 hcuts.2.2.2.2.1 hcuts.2.2.2.2.2 hpoint hdiffCell hgrid3
    rw [hshrink]
    have hrRc : r ≤ Rc := le_trans (min_le_right _ _) (by linarith : Rc / 2 ≤ Rc)
    exact hcert r hr hrRc
  exact
    RectangleGeometry.rectangleBoundaryIntegral_eq_sum_res (dirichletLogContourKernel x χ)
      (fun s ↦ 2 * Real.pi * Complex.I * dirichletLogResidueAt hne x s) S cells z w assignment hsum
      hdiff hsingular_res

/--
The height-sequence specialization of
`PseudoPrime.AnalyticNumberTheory.DirichletLFunction.dirichletLogFiniteContourIdentity`,
mirroring
`DirichletLFunction.dirichletReciprocalFiniteContourIdentity_heightSeq`.
-/
theorem dirichletLogFiniteContourIdentity_heightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (A k : ℕ) (hA : 2 ≤ A) :
    RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
        (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
        (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle χ hne
            (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k),
        2 * Real.pi * Complex.I * dirichletLogResidueAt hne x s := by
  obtain ⟨_, _, _, _, hre, him⟩ :=
    primitiveReciprocalCorners_facts hN2 hGRH hprimitive hne hinv hquad A k hA
  exact
    dirichletLogFiniteContourIdentity hx hprimitive hne hre him
      (primitiveHorizontalHeightSeq_singularities_mem_open hN2 hGRH hprimitive hne hinv hquad A k
        hA)

/-- Normalized form of the generic logarithmic finite-contour identity. -/
theorem dirichletLogFiniteContourIdentity_normalized {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hopen :
      ∀ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ) z w =
      ∑ s ∈ dirichletLFunctionSingularitiesInRectangle χ hne z w,
        dirichletLogResidueAt hne x s := by
  rw [dirichletLogFiniteContourIdentity hx hprimitive hne hre him hopen, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]
  rw [Complex.I_sq]
  ring

/--
The normalized log-kernel height-sequence contour identity, mirroring
`DirichletLFunction.dirichletReciprocalFiniteContourIdentity_heightSeq_normalized`.
-/
theorem dirichletLogFiniteContourIdentity_heightSeq_normalized {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 0 < x) (A k : ℕ) (hA : 2 ≤ A) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
          (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
          (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle χ hne
            (primitiveReciprocalLowerCorner hN2 hGRH hprimitive hne hinv hquad A k)
            (primitiveReciprocalUpperCorner hN2 hGRH hprimitive hne hinv hquad k),
        dirichletLogResidueAt hne x s := by
  rw [dirichletLogFiniteContourIdentity_heightSeq hN2 hGRH hprimitive hne hinv hquad hx A k hA,
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
    (-Complex.I / (2 * (Real.pi : ℂ))) * (2 * Real.pi * Complex.I * dirichletLogResidueAt hne x s) =
        ((-Complex.I / (2 * (Real.pi : ℂ))) * (2 * Real.pi * Complex.I)) *
          dirichletLogResidueAt hne x s :=
      by ring
    _ = dirichletLogResidueAt hne x s := by rw [hcoeff, one_mul]

/-!
The normalized logarithmic contour identity on the generic
GRH height-sequence rectangle.  This removes the quadratic-character restriction
from the finite residue identity and is the interface used by the boundary limit.
-/

theorem dirichletLogFiniteContourIdentity_heightSeq_normalized_of_grh {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (A k : ℕ)
    (hA : 2 ≤ A) :
    (-Complex.I / (2 * Real.pi)) *
        RectangleGeometry.rectangleBoundaryIntegral (dirichletLogContourKernel x χ)
          (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
          (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k) =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle χ hne
            (primitiveHeightSeqLowerCorner_of_grh hN2 hGRH hprimitive hne hinv A k)
            (primitiveHeightSeqUpperCorner_of_grh hN2 hGRH hprimitive hne hinv k),
        dirichletLogResidueAt hne x s := by
  obtain ⟨_, _, _, _, hre, him⟩ :=
    primitiveHeightSeqRectangleFacts_of_grh hN2 hGRH hprimitive hne hinv A k hA
  exact
    dirichletLogFiniteContourIdentity_normalized hx hprimitive hne hre him
      (primitiveHeightSeq_singularities_mem_open_of_grh hN2 hGRH hprimitive hne hinv A k hA)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
