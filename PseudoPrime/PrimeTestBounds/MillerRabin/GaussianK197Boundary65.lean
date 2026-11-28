/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary56
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch121539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch126539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 57 through 65 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def k197Seed62 : Edge :=
  ⟨126539, 126551028502105041, 126552040056599293, 406922726210478, 406927562467084⟩

private theorem k197_seed62_valid : Valid k197Seed62 :=
  (batch121539 k197_seed56_valid).1

private def k197Seed65 : Edge :=
  ⟨131539, 131526568479638167, 131527599263438967, 416443632175696, 416448666166048⟩

private theorem k197_seed65_valid : Valid k197Seed65 :=
  (batch126539 k197_seed62_valid).1

private def k197Rows57 : List SignedPsiRow :=
  [⟨125200, 126624, -41000000000000⟩]

private theorem k197_rows57_checked :
    signedWalk (gcdStep 121539 126625) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows57)
        5086 k197Seed56 =
      true := by
  decide +kernel

private theorem k197_psi_row57 {r : SignedPsiRow} (hr : r ∈ k197Rows57) (ha : 121539 ≤ r.left + 1)
    (hb : r.right < 126625) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed56_valid (by decide) (by decide) (by decide) k197_rows57_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 57. -/
public theorem psi_gaussian_k197_cell57 {x : ℝ} (hl : 125200 ≤ x) (hu : x ≤ 126624) :
    -41 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row57 (r := ⟨125200, 126624, -41000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows62 : List SignedPsiRow :=
  [⟨126677, 127392, -92000000000000⟩, ⟨127418, 128136, -112000000000000⟩,
    ⟨128162, 128882, -75000000000000⟩, ⟨128908, 130354, -31000000000000⟩,
    ⟨130406, 131861, -46000000000000⟩]

private theorem k197_rows62_checked :
    signedWalk (gcdStep 126539 131862) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows62)
        5323 k197Seed62 =
      true := by
  decide +kernel

private theorem k197_psi_row62 {r : SignedPsiRow} (hr : r ∈ k197Rows62) (ha : 126539 ≤ r.left + 1)
    (hb : r.right < 131862) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed62_valid (by decide) (by decide) (by decide) k197_rows62_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 58. -/
public theorem psi_gaussian_k197_cell58 {x : ℝ} (hl : 126677 ≤ x) (hu : x ≤ 127392) :
    -92 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row62 (r := ⟨126677, 127392, -92000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 59. -/
public theorem psi_gaussian_k197_cell59 {x : ℝ} (hl : 127418 ≤ x) (hu : x ≤ 128136) :
    -112 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row62 (r := ⟨127418, 128136, -112000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 60. -/
public theorem psi_gaussian_k197_cell60 {x : ℝ} (hl : 128162 ≤ x) (hu : x ≤ 128882) :
    -75 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row62 (r := ⟨128162, 128882, -75000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 61. -/
public theorem psi_gaussian_k197_cell61 {x : ℝ} (hl : 128908 ≤ x) (hu : x ≤ 130354) :
    -31 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row62 (r := ⟨128908, 130354, -31000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 62. -/
public theorem psi_gaussian_k197_cell62 {x : ℝ} (hl : 130406 ≤ x) (hu : x ≤ 131861) :
    -46 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row62 (r := ⟨130406, 131861, -46000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows65 : List SignedPsiRow :=
  [⟨131913, 133376, -66000000000000⟩, ⟨133429, 134901, -84000000000000⟩,
    ⟨134953, 136434, -89000000000000⟩]

private theorem k197_rows65_checked :
    signedWalk (gcdStep 131539 136435) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows65)
        4896 k197Seed65 =
      true := by
  decide +kernel

private theorem k197_psi_row65 {r : SignedPsiRow} (hr : r ∈ k197Rows65) (ha : 131539 ≤ r.left + 1)
    (hb : r.right < 136435) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed65_valid (by decide) (by decide) (by decide) k197_rows65_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 63. -/
public theorem psi_gaussian_k197_cell63 {x : ℝ} (hl : 131913 ≤ x) (hu : x ≤ 133376) :
    -66 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row65 (r := ⟨131913, 133376, -66000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 64. -/
public theorem psi_gaussian_k197_cell64 {x : ℝ} (hl : 133429 ≤ x) (hu : x ≤ 134901) :
    -84 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row65 (r := ⟨133429, 134901, -84000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 65. -/
public theorem psi_gaussian_k197_cell65 {x : ℝ} (hl : 134953 ≤ x) (hu : x ≤ 136434) :
    -89 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row65 (r := ⟨134953, 136434, -89000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
