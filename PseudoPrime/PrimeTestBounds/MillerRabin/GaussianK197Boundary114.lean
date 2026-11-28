/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary106
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin281539To321539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch271539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch276539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch321539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch326539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch331539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch336539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch341539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch346539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch351539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch356539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 113 and 114 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def boundarySeed276539 : Edge :=
  ⟨276539, 276639038602592967, 276641116711717283, 597241636923204, 597248712664322⟩

private theorem boundary_seed_276539_valid : Valid boundarySeed276539 :=
  (batch271539 boundary_seed_271539_valid).1

private def boundarySeed281539 : Edge :=
  ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩

private theorem boundary_seed_281539_valid : Valid boundarySeed281539 :=
  (batch276539 boundary_seed_276539_valid).1

private def boundarySeed321539 : Edge :=
  ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩

private theorem boundary_seed_321539_valid : Valid boundarySeed321539 :=
  (joined281539To321539 boundary_seed_281539_valid).1

private def boundarySeed326539 : Edge :=
  ⟨326539, 326618065632642258, 326620662106426693, 642526791887481, 642534922671444⟩

private theorem boundary_seed_326539_valid : Valid boundarySeed326539 :=
  (batch321539 boundary_seed_321539_valid).1

private def boundarySeed331539 : Edge :=
  ⟨331539, 331725008061551196, 331727639643786108, 642526791887481, 642534922671444⟩

private theorem boundary_seed_331539_valid : Valid boundarySeed331539 :=
  (batch326539 boundary_seed_326539_valid).1

private def boundarySeed336539 : Edge :=
  ⟨336539, 336666324708878478, 336669015912378774, 648884634152238, 648892766443253⟩

private theorem boundary_seed_336539_valid : Valid boundarySeed336539 :=
  (batch331539 boundary_seed_331539_valid).1

private def boundarySeed341539 : Edge :=
  ⟨341539, 341645214124329997, 341647926002239681, 648884634152238, 648892766443253⟩

private theorem boundary_seed_341539_valid : Valid boundarySeed341539 :=
  (batch336539 boundary_seed_336539_valid).1

private def boundarySeed346539 : Edge :=
  ⟨346539, 346700011368420178, 346702767638907207, 655259656683198, 655267971326173⟩

private theorem boundary_seed_346539_valid : Valid boundarySeed346539 :=
  (batch341539 boundary_seed_341539_valid).1

private def boundarySeed351539 : Edge :=
  ⟨351539, 351754154763738223, 351756956336323203, 655259656683198, 655267971326173⟩

private theorem boundary_seed_351539_valid : Valid boundarySeed351539 :=
  (batch346539 boundary_seed_346539_valid).1

private def boundarySeed356539 : Edge :=
  ⟨356539, 356781923285159961, 356784746846589057, 661644851080582, 661653167150248⟩

private theorem boundary_seed_356539_valid : Valid boundarySeed356539 :=
  (batch351539 boundary_seed_351539_valid).1

private def boundarySeed361539 : Edge :=
  ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩

private theorem boundary_seed_361539_valid : Valid boundarySeed361539 :=
  (batch356539 boundary_seed_356539_valid).1

private def rows321539 : List SignedPsiRow :=
  [⟨326302, 326539, 0⟩]

private theorem rows_321539_checked :
    signedWalk (gcdStep 321539 326540) (fun n ↦ signedRowFloor (-1000000000000000) n rows321539)
        5001 boundarySeed321539 =
      true := by
  decide +kernel

private theorem psi_row_321539 {r : SignedPsiRow} (hr : r ∈ rows321539) (ha : 321539 ≤ r.left + 1)
    (hb : r.right < 326540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_321539_valid (by decide) (by decide) (by decide)
    rows_321539_checked ha hb hlt hl hu

private theorem psi_cell113_from321539 {x : ℝ} (hl : 326302 ≤ x) (hu : x ≤ 326539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_321539 (r := ⟨326302, 326539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def rows326539 : List SignedPsiRow :=
  [⟨326539, 331539, 0⟩]

private theorem rows_326539_checked :
    signedWalk (gcdStep 326539 331540) (fun n ↦ signedRowFloor (-1000000000000000) n rows326539)
        5001 boundarySeed326539 =
      true := by
  decide +kernel

private theorem psi_row_326539 {r : SignedPsiRow} (hr : r ∈ rows326539) (ha : 326539 ≤ r.left + 1)
    (hb : r.right < 331540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_326539_valid (by decide) (by decide) (by decide)
    rows_326539_checked ha hb hlt hl hu

private theorem psi_cell113_from326539 {x : ℝ} (hl : 326539 ≤ x) (hu : x ≤ 331539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_326539 (r := ⟨326539, 331539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def rows331539 : List SignedPsiRow :=
  [⟨331539, 336539, 0⟩]

private theorem rows_331539_checked :
    signedWalk (gcdStep 331539 336540) (fun n ↦ signedRowFloor (-1000000000000000) n rows331539)
        5001 boundarySeed331539 =
      true := by
  decide +kernel

private theorem psi_row_331539 {r : SignedPsiRow} (hr : r ∈ rows331539) (ha : 331539 ≤ r.left + 1)
    (hb : r.right < 336540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_331539_valid (by decide) (by decide) (by decide)
    rows_331539_checked ha hb hlt hl hu

private theorem psi_cell113_from331539 {x : ℝ} (hl : 331539 ≤ x) (hu : x ≤ 336539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_331539 (r := ⟨331539, 336539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def rows336539 : List SignedPsiRow :=
  [⟨336539, 341539, 0⟩]

private theorem rows_336539_checked :
    signedWalk (gcdStep 336539 341540) (fun n ↦ signedRowFloor (-1000000000000000) n rows336539)
        5001 boundarySeed336539 =
      true := by
  decide +kernel

private theorem psi_row_336539 {r : SignedPsiRow} (hr : r ∈ rows336539) (ha : 336539 ≤ r.left + 1)
    (hb : r.right < 341540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_336539_valid (by decide) (by decide) (by decide)
    rows_336539_checked ha hb hlt hl hu

private theorem psi_cell113_from336539 {x : ℝ} (hl : 336539 ≤ x) (hu : x ≤ 341539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_336539 (r := ⟨336539, 341539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def rows341539 : List SignedPsiRow :=
  [⟨341539, 345151, 0⟩, ⟨345591, 346539, -13000000000000⟩]

private theorem rows_341539_checked :
    signedWalk (gcdStep 341539 346540) (fun n ↦ signedRowFloor (-1000000000000000) n rows341539)
        5001 boundarySeed341539 =
      true := by
  decide +kernel

private theorem psi_row_341539 {r : SignedPsiRow} (hr : r ∈ rows341539) (ha : 341539 ≤ r.left + 1)
    (hb : r.right < 346540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_341539_valid (by decide) (by decide) (by decide)
    rows_341539_checked ha hb hlt hl hu

private theorem psi_cell113_from341539 {x : ℝ} (hl : 341539 ≤ x) (hu : x ≤ 345151) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_341539 (r := ⟨341539, 345151, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private theorem psi_cell114_from341539 {x : ℝ} (hl : 345591 ≤ x) (hu : x ≤ 346539) :
    -13 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_341539 (r := ⟨345591, 346539, -13000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows346539 : List SignedPsiRow :=
  [⟨346539, 351539, -13000000000000⟩]

private theorem rows_346539_checked :
    signedWalk (gcdStep 346539 351540) (fun n ↦ signedRowFloor (-1000000000000000) n rows346539)
        5001 boundarySeed346539 =
      true := by
  decide +kernel

private theorem psi_row_346539 {r : SignedPsiRow} (hr : r ∈ rows346539) (ha : 346539 ≤ r.left + 1)
    (hb : r.right < 351540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_346539_valid (by decide) (by decide) (by decide)
    rows_346539_checked ha hb hlt hl hu

private theorem psi_cell114_from346539 {x : ℝ} (hl : 346539 ≤ x) (hu : x ≤ 351539) :
    -13 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_346539 (r := ⟨346539, 351539, -13000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows351539 : List SignedPsiRow :=
  [⟨351539, 356539, -13000000000000⟩]

private theorem rows_351539_checked :
    signedWalk (gcdStep 351539 356540) (fun n ↦ signedRowFloor (-1000000000000000) n rows351539)
        5001 boundarySeed351539 =
      true := by
  decide +kernel

private theorem psi_row_351539 {r : SignedPsiRow} (hr : r ∈ rows351539) (ha : 351539 ≤ r.left + 1)
    (hb : r.right < 356540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_351539_valid (by decide) (by decide) (by decide)
    rows_351539_checked ha hb hlt hl hu

private theorem psi_cell114_from351539 {x : ℝ} (hl : 351539 ≤ x) (hu : x ≤ 356539) :
    -13 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_351539 (r := ⟨351539, 356539, -13000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows356539 : List SignedPsiRow :=
  [⟨356539, 361539, -13000000000000⟩]

private theorem rows_356539_checked :
    signedWalk (gcdStep 356539 361540) (fun n ↦ signedRowFloor (-1000000000000000) n rows356539)
        5001 boundarySeed356539 =
      true := by
  decide +kernel

private theorem psi_row_356539 {r : SignedPsiRow} (hr : r ∈ rows356539) (ha : 356539 ≤ r.left + 1)
    (hb : r.right < 361540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_356539_valid (by decide) (by decide) (by decide)
    rows_356539_checked ha hb hlt hl hu

private theorem psi_cell114_from356539 {x : ℝ} (hl : 356539 ≤ x) (hu : x ≤ 361539) :
    -13 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_356539 (r := ⟨356539, 361539, -13000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows361539 : List SignedPsiRow :=
  [⟨361539, 364994, -13000000000000⟩]

private theorem rows_361539_checked :
    signedWalk (gcdStep 361539 364995) (fun n ↦ signedRowFloor (-1000000000000000) n rows361539)
        3456 boundarySeed361539 =
      true := by
  decide +kernel

private theorem psi_row_361539 {r : SignedPsiRow} (hr : r ∈ rows361539) (ha : 361539 ≤ r.left + 1)
    (hb : r.right < 364995) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_361539_valid (by decide) (by decide) (by decide)
    rows_361539_checked ha hb hlt hl hu

private theorem psi_cell114_from361539 {x : ℝ} (hl : 361539 ≤ x) (hu : x ≤ 364994) :
    -13 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_361539 (r := ⟨361539, 364994, -13000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 113. -/
public theorem psi_gaussian_k197_cell113 {x : ℝ} (hl : 326302 ≤ x) (hu : x ≤ 345151) :
    0 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 326539
  · exact psi_cell113_from321539 hl h0
  by_cases h1 : x ≤ 331539
  · exact psi_cell113_from326539 (le_of_not_ge h0) h1
  by_cases h2 : x ≤ 336539
  · exact psi_cell113_from331539 (le_of_not_ge h1) h2
  by_cases h3 : x ≤ 341539
  · exact psi_cell113_from336539 (le_of_not_ge h2) h3
  exact psi_cell113_from341539 (le_of_not_ge h3) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 114. -/
public theorem psi_gaussian_k197_cell114 {x : ℝ} (hl : 345591 ≤ x) (hu : x ≤ 364994) :
    -13 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 346539
  · exact psi_cell114_from341539 hl h0
  by_cases h1 : x ≤ 351539
  · exact psi_cell114_from346539 (le_of_not_ge h0) h1
  by_cases h2 : x ≤ 356539
  · exact psi_cell114_from351539 (le_of_not_ge h1) h2
  by_cases h3 : x ≤ 361539
  · exact psi_cell114_from356539 (le_of_not_ge h2) h3
  exact psi_cell114_from361539 (le_of_not_ge h3) hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
