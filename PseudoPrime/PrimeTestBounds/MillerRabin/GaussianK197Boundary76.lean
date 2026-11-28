/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary65
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch131539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch136539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch141539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch146539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 66 through 76 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def boundarySeed136539 : Edge :=
  ⟨136539, 136620934511478539, 136622021341265911, 422348991608372, 422354214641944⟩

private theorem boundary_seed_136539_valid : Valid boundarySeed136539 :=
  (batch131539 k197_seed65_valid).1

private def boundarySeed141539 : Edge :=
  ⟨141539, 141624410084419827, 141625553194246354, 428270569200360, 428275884536636⟩

private theorem boundary_seed_141539_valid : Valid boundarySeed141539 :=
  (batch136539 boundary_seed_136539_valid).1

private def boundarySeed146539 : Edge :=
  ⟨146539, 146524007745593682, 146525211438669482, 434208105237132, 434213452403432⟩

private theorem boundary_seed_146539_valid : Valid boundarySeed146539 :=
  (batch141539 boundary_seed_141539_valid).1

private def boundarySeed151539 : Edge :=
  ⟨151539, 151638276828159825, 151639551791847855, 450090008633458, 450095613867576⟩

private theorem boundary_seed_151539_valid : Valid boundarySeed151539 :=
  (batch146539 boundary_seed_146539_valid).1

private def k197Rows66 : List SignedPsiRow :=
  [⟨136486, 137975, 0⟩]

private theorem k197_rows66_checked :
    signedWalk (gcdStep 131539 137976) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows66)
        6437 k197Seed65 =
      true := by
  decide +kernel

private theorem k197_psi_row66 {r : SignedPsiRow} (hr : r ∈ k197Rows66) (ha : 131539 ≤ r.left + 1)
    (hb : r.right < 137976) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed65_valid (by decide) (by decide) (by decide) k197_rows66_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 66. -/
public theorem psi_gaussian_k197_cell66 {x : ℝ} (hl : 136486 ≤ x) (hu : x ≤ 137975) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row66 (r := ⟨136486, 137975, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def k197Rows69 : List SignedPsiRow :=
  [⟨138028, 139526, -14000000000000⟩, ⟨139578, 141084, 0⟩, ⟨141137, 142652, 0⟩]

private theorem k197_rows69_checked :
    signedWalk (gcdStep 136539 142653) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows69)
        6114 boundarySeed136539 =
      true := by
  decide +kernel

private theorem k197_psi_row69 {r : SignedPsiRow} (hr : r ∈ k197Rows69) (ha : 136539 ≤ r.left + 1)
    (hb : r.right < 142653) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_136539_valid (by decide) (by decide) (by decide)
    k197_rows69_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 67. -/
public theorem psi_gaussian_k197_cell67 {x : ℝ} (hl : 138028 ≤ x) (hu : x ≤ 139526) :
    -14 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row69 (r := ⟨138028, 139526, -14000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 68. -/
public theorem psi_gaussian_k197_cell68 {x : ℝ} (hl : 139578 ≤ x) (hu : x ≤ 141084) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row69 (r := ⟨139578, 141084, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 69. -/
public theorem psi_gaussian_k197_cell69 {x : ℝ} (hl : 141137 ≤ x) (hu : x ≤ 142652) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row69 (r := ⟨141137, 142652, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def k197Rows72 : List SignedPsiRow :=
  [⟨142705, 144228, -39000000000000⟩, ⟨144281, 145813, -94000000000000⟩,
    ⟨145866, 147407, -50000000000000⟩]

private theorem k197_rows72_checked :
    signedWalk (gcdStep 141539 147408) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows72)
        5869 boundarySeed141539 =
      true := by
  decide +kernel

private theorem k197_psi_row72 {r : SignedPsiRow} (hr : r ∈ k197Rows72) (ha : 141539 ≤ r.left + 1)
    (hb : r.right < 147408) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_141539_valid (by decide) (by decide) (by decide)
    k197_rows72_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 70. -/
public theorem psi_gaussian_k197_cell70 {x : ℝ} (hl : 142705 ≤ x) (hu : x ≤ 144228) :
    -39 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row72 (r := ⟨142705, 144228, -39000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 71. -/
public theorem psi_gaussian_k197_cell71 {x : ℝ} (hl : 144281 ≤ x) (hu : x ≤ 145813) :
    -94 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row72 (r := ⟨144281, 145813, -94000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 72. -/
public theorem psi_gaussian_k197_cell72 {x : ℝ} (hl : 145866 ≤ x) (hu : x ≤ 147407) :
    -50 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row72 (r := ⟨145866, 147407, -50000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows75 : List SignedPsiRow :=
  [⟨147459, 149009, -86000000000000⟩, ⟨149061, 150620, -24000000000000⟩, ⟨150619, 152185, 0⟩]

private theorem k197_rows75_checked :
    signedWalk (gcdStep 146539 152186) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows75)
        5647 boundarySeed146539 =
      true := by
  decide +kernel

private theorem k197_psi_row75 {r : SignedPsiRow} (hr : r ∈ k197Rows75) (ha : 146539 ≤ r.left + 1)
    (hb : r.right < 152186) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_146539_valid (by decide) (by decide) (by decide)
    k197_rows75_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 73. -/
public theorem psi_gaussian_k197_cell73 {x : ℝ} (hl : 147459 ≤ x) (hu : x ≤ 149009) :
    -86 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row75 (r := ⟨147459, 149009, -86000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 74. -/
public theorem psi_gaussian_k197_cell74 {x : ℝ} (hl : 149061 ≤ x) (hu : x ≤ 150620) :
    -24 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row75 (r := ⟨149061, 150620, -24000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 75. -/
public theorem psi_gaussian_k197_cell75 {x : ℝ} (hl : 150619 ≤ x) (hu : x ≤ 152185) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row75 (r := ⟨150619, 152185, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def k197Rows76 : List SignedPsiRow :=
  [⟨152292, 155450, 0⟩]

private theorem k197_rows76_checked :
    signedWalk (gcdStep 151539 155451) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows76)
        3912 boundarySeed151539 =
      true := by
  decide +kernel

private theorem k197_psi_row76 {r : SignedPsiRow} (hr : r ∈ k197Rows76) (ha : 151539 ≤ r.left + 1)
    (hb : r.right < 155451) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_151539_valid (by decide) (by decide) (by decide)
    k197_rows76_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 76. -/
public theorem psi_gaussian_k197_cell76 {x : ℝ} (hl : 152292 ≤ x) (hu : x ≤ 155450) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row76 (r := ⟨152292, 155450, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
