/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary45
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch116539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiQuarterBridge
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 46 through 56 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def k197Seed56 : Edge :=
  ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩

private theorem k197_seed56_valid : Valid k197Seed56 :=
  (batch116539 k197_seed45_valid).1

private def k197Rows51 : List SignedPsiRow :=
  [⟨119739, 120087, -130000000000000⟩, ⟨120099, 120448, -122000000000000⟩,
    ⟨120460, 120635, -155000000000000⟩, ⟨120634, 120809, -140000000000000⟩,
    ⟨120821, 121171, -112000000000000⟩, ⟨121170, 121520, -91000000000000⟩]

private theorem k197_rows51_checked :
    signedWalk (gcdStep 116539 121521) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows51)
        4982 k197Seed45 =
      true := by
  decide +kernel

private theorem k197_psi_row51 {r : SignedPsiRow} (hr : r ∈ k197Rows51) (ha : 116539 ≤ r.left + 1)
    (hb : r.right < 121521) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed45_valid (by decide) (by decide) (by decide) k197_rows51_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 46. -/
public theorem psi_gaussian_k197_cell46 {x : ℝ} (hl : 119739 ≤ x) (hu : x ≤ 120087) :
    -130 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row51 (r := ⟨119739, 120087, -130000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 47. -/
public theorem psi_gaussian_k197_cell47 {x : ℝ} (hl : 120099 ≤ x) (hu : x ≤ 120448) :
    -122 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row51 (r := ⟨120099, 120448, -122000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 48. -/
public theorem psi_gaussian_k197_cell48 {x : ℝ} (hl : 120460 ≤ x) (hu : x ≤ 120635) :
    -155 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row51 (r := ⟨120460, 120635, -155000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 49. -/
public theorem psi_gaussian_k197_cell49 {x : ℝ} (hl : 120634 ≤ x) (hu : x ≤ 120809) :
    -140 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row51 (r := ⟨120634, 120809, -140000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 50. -/
public theorem psi_gaussian_k197_cell50 {x : ℝ} (hl : 120821 ≤ x) (hu : x ≤ 121171) :
    -112 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row51 (r := ⟨120821, 121171, -112000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 51. -/
public theorem psi_gaussian_k197_cell51 {x : ℝ} (hl : 121170 ≤ x) (hu : x ≤ 121520) :
    -91 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row51 (r := ⟨121170, 121520, -91000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows56 : List SignedPsiRow :=
  [⟨121546, 122247, -68000000000000⟩, ⟨122272, 122975, -29000000000000⟩,
    ⟨123001, 123706, -67000000000000⟩, ⟨123732, 124439, -41000000000000⟩,
    ⟨124438, 125147, -34000000000000⟩]

private theorem k197_rows56_checked :
    signedWalk (gcdStep 121539 125148) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows56)
        3609 k197Seed56 =
      true := by
  decide +kernel

private theorem k197_psi_row56 {r : SignedPsiRow} (hr : r ∈ k197Rows56) (ha : 121539 ≤ r.left + 1)
    (hb : r.right < 125148) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed56_valid (by decide) (by decide) (by decide) k197_rows56_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 52. -/
public theorem psi_gaussian_k197_cell52 {x : ℝ} (hl : 121546 ≤ x) (hu : x ≤ 122247) :
    -68 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row56 (r := ⟨121546, 122247, -68000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 53. -/
public theorem psi_gaussian_k197_cell53 {x : ℝ} (hl : 122272 ≤ x) (hu : x ≤ 122975) :
    -29 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row56 (r := ⟨122272, 122975, -29000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 54. -/
public theorem psi_gaussian_k197_cell54 {x : ℝ} (hl : 123001 ≤ x) (hu : x ≤ 123706) :
    -67 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row56 (r := ⟨123001, 123706, -67000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 55. -/
public theorem psi_gaussian_k197_cell55 {x : ℝ} (hl : 123732 ≤ x) (hu : x ≤ 124439) :
    -41 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row56 (r := ⟨123732, 124439, -41000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 56. -/
public theorem psi_gaussian_k197_cell56 {x : ℝ} (hl : 124438 ≤ x) (hu : x ≤ 125147) :
    -34 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row56 (r := ⟨124438, 125147, -34000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
