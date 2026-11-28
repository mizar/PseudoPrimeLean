/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiQuarterBridge
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 37 through 45 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def k197Seed45 : Edge :=
  ⟨116539, 116486170396305392, 116487141911824128, 387405952542179, 387410641104636⟩

private theorem k197_seed45_valid : Valid k197Seed45 :=
  (batch111539 (batch106539 bridge_start_valid).1).1

private def k197Rows45 : List SignedPsiRow :=
  [⟨117589, 117933, -122000000000000⟩, ⟨117946, 118291, -79000000000000⟩,
    ⟨118303, 118649, -113000000000000⟩, ⟨118661, 119008, -116000000000000⟩,
    ⟨119020, 119367, -135000000000000⟩, ⟨119039, 119367, -123000000000000⟩,
    ⟨119379, 119467, -143000000000000⟩, ⟨119466, 119510, -167000000000000⟩,
    ⟨119509, 119553, -177000000000000⟩, ⟨119559, 119733, -170000000000000⟩,
    ⟨119611, 119733, -164000000000000⟩]

private theorem k197_rows45_checked :
    signedWalk (gcdStep 116539 119734) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows45)
        3195 k197Seed45 =
      true := by
  decide +kernel

private theorem k197_psi_row45 {r : SignedPsiRow} (hr : r ∈ k197Rows45) (ha : 116539 ≤ r.left + 1)
    (hb : r.right < 119734) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed45_valid (by decide) (by decide) (by decide) k197_rows45_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 37. -/
public theorem psi_gaussian_k197_cell37 {x : ℝ} (hl : 117589 ≤ x) (hu : x ≤ 117933) :
    -122 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨117589, 117933, -122000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 38. -/
public theorem psi_gaussian_k197_cell38 {x : ℝ} (hl : 117946 ≤ x) (hu : x ≤ 118291) :
    -79 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨117946, 118291, -79000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 39. -/
public theorem psi_gaussian_k197_cell39 {x : ℝ} (hl : 118303 ≤ x) (hu : x ≤ 118649) :
    -113 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨118303, 118649, -113000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 40. -/
public theorem psi_gaussian_k197_cell40 {x : ℝ} (hl : 118661 ≤ x) (hu : x ≤ 119008) :
    -116 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨118661, 119008, -116000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 41. -/
public theorem psi_gaussian_k197_cell41 {x : ℝ} (hl : 119020 ≤ x) (hu : x ≤ 119367) :
    -135 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119020, 119367, -135000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev bound after the first primes of K197 cell 41. -/
public theorem psi_gaussian_k197_cell41_right {x : ℝ} (hl : 119039 ≤ x) (hu : x ≤ 119367) :
    -123 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119039, 119367, -123000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 42. -/
public theorem psi_gaussian_k197_cell42 {x : ℝ} (hl : 119379 ≤ x) (hu : x ≤ 119467) :
    -143 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119379, 119467, -143000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 43. -/
public theorem psi_gaussian_k197_cell43 {x : ℝ} (hl : 119466 ≤ x) (hu : x ≤ 119510) :
    -167 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119466, 119510, -167000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 44. -/
public theorem psi_gaussian_k197_cell44 {x : ℝ} (hl : 119509 ≤ x) (hu : x ≤ 119553) :
    -177 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119509, 119553, -177000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 45. -/
public theorem psi_gaussian_k197_cell45 {x : ℝ} (hl : 119559 ≤ x) (hu : x ≤ 119733) :
    -170 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119559, 119733, -170000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- After the prime at 119611, the signed floor on the rest of K197 cell 45 is -164. -/
public theorem psi_gaussian_k197_cell45_right {x : ℝ} (hl : 119611 ≤ x) (hu : x ≤ 119733) :
    -164 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row45 (r := ⟨119611, 119733, -164000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
