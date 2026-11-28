/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary99
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch216539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch221539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch226539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch231539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch236539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch241539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch246539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch251539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch256539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch261539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch266539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 100 through 106 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def boundarySeed221539 : Edge :=
  ⟨221539, 221562348463509236, 221564110857657096, 542700239780932, 542706527944601⟩

private theorem boundary_seed_221539_valid : Valid boundarySeed221539 :=
  (batch216539 boundary_seed_216539_valid).1

private def boundarySeed226539 : Edge :=
  ⟨226539, 226564048406585613, 226565830273712052, 542700239780932, 542706527944601⟩

private theorem boundary_seed_226539_valid : Valid boundarySeed226539 :=
  (batch221539 boundary_seed_221539_valid).1

private def boundarySeed231539 : Edge :=
  ⟨231539, 231745495560216332, 231747298600661942, 552982813167160, 552989211302836⟩

private theorem boundary_seed_231539_valid : Valid boundarySeed231539 :=
  (batch226539 boundary_seed_226539_valid).1

private def boundarySeed236539 : Edge :=
  ⟨236539, 236480611358270303, 236482434983938771, 552982813167160, 552989211302836⟩

private theorem boundary_seed_236539_valid : Valid boundarySeed236539 :=
  (batch231539 boundary_seed_231539_valid).1

private def boundarySeed241539 : Edge :=
  ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩

private theorem boundary_seed_241539_valid : Valid boundarySeed241539 :=
  (batch236539 boundary_seed_236539_valid).1

private def boundarySeed246539 : Edge :=
  ⟨246539, 246507999558840910, 246509865452694879, 565367520318279, 565374043686911⟩

private theorem boundary_seed_246539_valid : Valid boundarySeed246539 :=
  (batch241539 boundary_seed_241539_valid).1

private def boundarySeed251539 : Edge :=
  ⟨251539, 251645861104826777, 251647743667137801, 571580126340599, 571586668000734⟩

private theorem boundary_seed_251539_valid : Valid boundarySeed251539 :=
  (batch246539 boundary_seed_246539_valid).1

private def boundarySeed256539 : Edge :=
  ⟨256539, 256605331295637934, 256607231429693859, 577800715583523, 577807356830686⟩

private theorem boundary_seed_256539_valid : Valid boundarySeed256539 :=
  (batch251539 boundary_seed_251539_valid).1

private def boundarySeed261539 : Edge :=
  ⟨261539, 261447865457459711, 261449783722830360, 584033163277008, 584039853733679⟩

private theorem boundary_seed_261539_valid : Valid boundarySeed261539 :=
  (batch256539 boundary_seed_256539_valid).1

private def boundarySeed266539 : Edge :=
  ⟨266539, 266454596163441081, 266456536110049775, 584726310457567, 584733000914240⟩

private theorem boundary_seed_266539_valid : Valid boundarySeed266539 :=
  (batch261539 boundary_seed_261539_valid).1

private def boundarySeed271539 : Edge :=
  ⟨271539, 271636849207892232, 271638883120549580, 590982058712358, 590988903664281⟩

private theorem boundary_seed_271539_valid : Valid boundarySeed271539 :=
  (batch266539 boundary_seed_266539_valid).1

private def rows221539 : List SignedPsiRow :=
  [⟨222198, 226539, -51000000000000⟩]

private theorem rows_221539_checked :
    signedWalk (gcdStep 221539 226540) (fun n ↦ signedRowFloor (-1000000000000000) n rows221539)
        5001 boundarySeed221539 =
      true := by
  decide +kernel

private theorem psi_row_221539 {r : SignedPsiRow} (hr : r ∈ rows221539) (ha : 221539 ≤ r.left + 1)
    (hb : r.right < 226540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_221539_valid (by decide) (by decide) (by decide)
    rows_221539_checked ha hb hlt hl hu

private theorem psi_cell100_from221539 {x : ℝ} (hl : 222198 ≤ x) (hu : x ≤ 226539) :
    -51 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_221539 (r := ⟨222198, 226539, -51000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows226539 : List SignedPsiRow :=
  [⟨226539, 229896, -51000000000000⟩, ⟨230112, 231539, -16000000000000⟩]

private theorem rows_226539_checked :
    signedWalk (gcdStep 226539 231540) (fun n ↦ signedRowFloor (-1000000000000000) n rows226539)
        5001 boundarySeed226539 =
      true := by
  decide +kernel

private theorem psi_row_226539 {r : SignedPsiRow} (hr : r ∈ rows226539) (ha : 226539 ≤ r.left + 1)
    (hb : r.right < 231540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_226539_valid (by decide) (by decide) (by decide)
    rows_226539_checked ha hb hlt hl hu

private theorem psi_cell100_from226539 {x : ℝ} (hl : 226539 ≤ x) (hu : x ≤ 229896) :
    -51 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_226539 (r := ⟨226539, 229896, -51000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private theorem psi_cell101_from226539 {x : ℝ} (hl : 230112 ≤ x) (hu : x ≤ 231539) :
    -16 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_226539 (r := ⟨230112, 231539, -16000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows231539 : List SignedPsiRow :=
  [⟨231539, 234014, -16000000000000⟩, ⟨234121, 236539, -198000000000000⟩]

private theorem rows_231539_checked :
    signedWalk (gcdStep 231539 236540) (fun n ↦ signedRowFloor (-1000000000000000) n rows231539)
        5001 boundarySeed231539 =
      true := by
  decide +kernel

private theorem psi_row_231539 {r : SignedPsiRow} (hr : r ∈ rows231539) (ha : 231539 ≤ r.left + 1)
    (hb : r.right < 236540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_231539_valid (by decide) (by decide) (by decide)
    rows_231539_checked ha hb hlt hl hu

private theorem psi_cell101_from231539 {x : ℝ} (hl : 231539 ≤ x) (hu : x ≤ 234014) :
    -16 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_231539 (r := ⟨231539, 234014, -16000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private theorem psi_cell102_from231539 {x : ℝ} (hl : 234121 ≤ x) (hu : x ≤ 236539) :
    -198 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_231539 (r := ⟨234121, 236539, -198000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows236539 : List SignedPsiRow :=
  [⟨236539, 238058, -198000000000000⟩, ⟨238164, 241539, -145000000000000⟩]

private theorem rows_236539_checked :
    signedWalk (gcdStep 236539 241540) (fun n ↦ signedRowFloor (-1000000000000000) n rows236539)
        5001 boundarySeed236539 =
      true := by
  decide +kernel

private theorem psi_row_236539 {r : SignedPsiRow} (hr : r ∈ rows236539) (ha : 236539 ≤ r.left + 1)
    (hb : r.right < 241540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_236539_valid (by decide) (by decide) (by decide)
    rows_236539_checked ha hb hlt hl hu

private theorem psi_cell102_from236539 {x : ℝ} (hl : 236539 ≤ x) (hu : x ≤ 238058) :
    -198 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_236539 (r := ⟨236539, 238058, -198000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private theorem psi_cell103_from236539 {x : ℝ} (hl : 238164 ≤ x) (hu : x ≤ 241539) :
    -145 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_236539 (r := ⟨238164, 241539, -145000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows241539 : List SignedPsiRow :=
  [⟨241539, 246139, -145000000000000⟩, ⟨246355, 246539, -84000000000000⟩]

private theorem rows_241539_checked :
    signedWalk (gcdStep 241539 246540) (fun n ↦ signedRowFloor (-1000000000000000) n rows241539)
        5001 boundarySeed241539 =
      true := by
  decide +kernel

private theorem psi_row_241539 {r : SignedPsiRow} (hr : r ∈ rows241539) (ha : 241539 ≤ r.left + 1)
    (hb : r.right < 246540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_241539_valid (by decide) (by decide) (by decide)
    rows_241539_checked ha hb hlt hl hu

private theorem psi_cell103_from241539 {x : ℝ} (hl : 241539 ≤ x) (hu : x ≤ 246139) :
    -145 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_241539 (r := ⟨241539, 246139, -145000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private theorem psi_cell104_from241539 {x : ℝ} (hl : 246355 ≤ x) (hu : x ≤ 246539) :
    -84 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_241539 (r := ⟨246355, 246539, -84000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows246539 : List SignedPsiRow :=
  [⟨246539, 251539, -84000000000000⟩]

private theorem rows_246539_checked :
    signedWalk (gcdStep 246539 251540) (fun n ↦ signedRowFloor (-1000000000000000) n rows246539)
        5001 boundarySeed246539 =
      true := by
  decide +kernel

private theorem psi_row_246539 {r : SignedPsiRow} (hr : r ∈ rows246539) (ha : 246539 ≤ r.left + 1)
    (hb : r.right < 251540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_246539_valid (by decide) (by decide) (by decide)
    rows_246539_checked ha hb hlt hl hu

private theorem psi_cell104_from246539 {x : ℝ} (hl : 246539 ≤ x) (hu : x ≤ 251539) :
    -84 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_246539 (r := ⟨246539, 251539, -84000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows251539 : List SignedPsiRow :=
  [⟨251539, 254468, -84000000000000⟩, ⟨254684, 256539, -157000000000000⟩]

private theorem rows_251539_checked :
    signedWalk (gcdStep 251539 256540) (fun n ↦ signedRowFloor (-1000000000000000) n rows251539)
        5001 boundarySeed251539 =
      true := by
  decide +kernel

private theorem psi_row_251539 {r : SignedPsiRow} (hr : r ∈ rows251539) (ha : 251539 ≤ r.left + 1)
    (hb : r.right < 256540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_251539_valid (by decide) (by decide) (by decide)
    rows_251539_checked ha hb hlt hl hu

private theorem psi_cell104_from251539 {x : ℝ} (hl : 251539 ≤ x) (hu : x ≤ 254468) :
    -84 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_251539 (r := ⟨251539, 254468, -84000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private theorem psi_cell105_from251539 {x : ℝ} (hl : 254684 ≤ x) (hu : x ≤ 256539) :
    -157 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_251539 (r := ⟨254684, 256539, -157000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows256539 : List SignedPsiRow :=
  [⟨256539, 261539, -157000000000000⟩]

private theorem rows_256539_checked :
    signedWalk (gcdStep 256539 261540) (fun n ↦ signedRowFloor (-1000000000000000) n rows256539)
        5001 boundarySeed256539 =
      true := by
  decide +kernel

private theorem psi_row_256539 {r : SignedPsiRow} (hr : r ∈ rows256539) (ha : 256539 ≤ r.left + 1)
    (hb : r.right < 261540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_256539_valid (by decide) (by decide) (by decide)
    rows_256539_checked ha hb hlt hl hu

private theorem psi_cell105_from256539 {x : ℝ} (hl : 256539 ≤ x) (hu : x ≤ 261539) :
    -157 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_256539 (r := ⟨256539, 261539, -157000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows261539 : List SignedPsiRow :=
  [⟨261539, 262936, -157000000000000⟩, ⟨263152, 266539, -175000000000000⟩]

private theorem rows_261539_checked :
    signedWalk (gcdStep 261539 266540) (fun n ↦ signedRowFloor (-1000000000000000) n rows261539)
        5001 boundarySeed261539 =
      true := by
  decide +kernel

private theorem psi_row_261539 {r : SignedPsiRow} (hr : r ∈ rows261539) (ha : 261539 ≤ r.left + 1)
    (hb : r.right < 266540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_261539_valid (by decide) (by decide) (by decide)
    rows_261539_checked ha hb hlt hl hu

private theorem psi_cell105_from261539 {x : ℝ} (hl : 261539 ≤ x) (hu : x ≤ 262936) :
    -157 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_261539 (r := ⟨261539, 262936, -157000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private theorem psi_cell106_from261539 {x : ℝ} (hl : 263152 ≤ x) (hu : x ≤ 266539) :
    -175 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_261539 (r := ⟨263152, 266539, -175000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows266539 : List SignedPsiRow :=
  [⟨266539, 271539, -175000000000000⟩]

private theorem rows_266539_checked :
    signedWalk (gcdStep 266539 271540) (fun n ↦ signedRowFloor (-1000000000000000) n rows266539)
        5001 boundarySeed266539 =
      true := by
  decide +kernel

private theorem psi_row_266539 {r : SignedPsiRow} (hr : r ∈ rows266539) (ha : 266539 ≤ r.left + 1)
    (hb : r.right < 271540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_266539_valid (by decide) (by decide) (by decide)
    rows_266539_checked ha hb hlt hl hu

private theorem psi_cell106_from266539 {x : ℝ} (hl : 266539 ≤ x) (hu : x ≤ 271539) :
    -175 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_266539 (r := ⟨266539, 271539, -175000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def rows271539 : List SignedPsiRow :=
  [⟨271539, 271542, -175000000000000⟩]

private theorem rows_271539_checked :
    signedWalk (gcdStep 271539 271543) (fun n ↦ signedRowFloor (-1000000000000000) n rows271539) 4
        boundarySeed271539 =
      true := by
  decide +kernel

private theorem psi_row_271539 {r : SignedPsiRow} (hr : r ∈ rows271539) (ha : 271539 ≤ r.left + 1)
    (hb : r.right < 271543) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_271539_valid (by decide) (by decide) (by decide)
    rows_271539_checked ha hb hlt hl hu

private theorem psi_cell106_from271539 {x : ℝ} (hl : 271539 ≤ x) (hu : x ≤ 271542) :
    -175 ≤ Chebyshev.psi x - x := by
  have h :=
    psi_row_271539 (r := ⟨271539, 271542, -175000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 100. -/
public theorem psi_gaussian_k197_cell100 {x : ℝ} (hl : 222198 ≤ x) (hu : x ≤ 229896) :
    -51 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 226539
  · exact psi_cell100_from221539 hl h0
  exact psi_cell100_from226539 (le_of_not_ge h0) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 101. -/
public theorem psi_gaussian_k197_cell101 {x : ℝ} (hl : 230112 ≤ x) (hu : x ≤ 234014) :
    -16 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 231539
  · exact psi_cell101_from226539 hl h0
  exact psi_cell101_from231539 (le_of_not_ge h0) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 102. -/
public theorem psi_gaussian_k197_cell102 {x : ℝ} (hl : 234121 ≤ x) (hu : x ≤ 238058) :
    -198 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 236539
  · exact psi_cell102_from231539 hl h0
  exact psi_cell102_from236539 (le_of_not_ge h0) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 103. -/
public theorem psi_gaussian_k197_cell103 {x : ℝ} (hl : 238164 ≤ x) (hu : x ≤ 246139) :
    -145 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 241539
  · exact psi_cell103_from236539 hl h0
  exact psi_cell103_from241539 (le_of_not_ge h0) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 104. -/
public theorem psi_gaussian_k197_cell104 {x : ℝ} (hl : 246355 ≤ x) (hu : x ≤ 254468) :
    -84 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 246539
  · exact psi_cell104_from241539 hl h0
  by_cases h1 : x ≤ 251539
  · exact psi_cell104_from246539 (le_of_not_ge h0) h1
  exact psi_cell104_from251539 (le_of_not_ge h1) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 105. -/
public theorem psi_gaussian_k197_cell105 {x : ℝ} (hl : 254684 ≤ x) (hu : x ≤ 262936) :
    -157 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 256539
  · exact psi_cell105_from251539 hl h0
  by_cases h1 : x ≤ 261539
  · exact psi_cell105_from256539 (le_of_not_ge h0) h1
  exact psi_cell105_from261539 (le_of_not_ge h1) hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 106. -/
public theorem psi_gaussian_k197_cell106 {x : ℝ} (hl : 263152 ≤ x) (hu : x ≤ 271542) :
    -175 ≤ Chebyshev.psi x - x := by
  by_cases h0 : x ≤ 266539
  · exact psi_cell106_from261539 hl h0
  by_cases h1 : x ≤ 271539
  · exact psi_cell106_from266539 (le_of_not_ge h0) h1
  exact psi_cell106_from271539 (le_of_not_ge h1) hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
