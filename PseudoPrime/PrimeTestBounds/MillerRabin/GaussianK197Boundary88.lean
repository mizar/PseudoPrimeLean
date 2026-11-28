/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary76
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch151539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch156539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch161539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch166539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch171539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 77 through 88 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def boundarySeed156539 : Edge :=
  ⟨156539, 156595255550532633, 156596572739483630, 450090008633458, 450095613867576⟩

private theorem boundary_seed_156539_valid : Valid boundarySeed156539 :=
  (batch151539 boundary_seed_151539_valid).1

private def boundarySeed161539 : Edge :=
  ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩

private theorem boundary_seed_161539_valid : Valid boundarySeed161539 :=
  (batch156539 boundary_seed_156539_valid).1

private def boundarySeed166539 : Edge :=
  ⟨166539, 166382984002285436, 166384385504926919, 464465800923861, 464471490629316⟩

private theorem boundary_seed_166539_valid : Valid boundarySeed166539 :=
  (batch161539 boundary_seed_161539_valid).1

private def boundarySeed171539 : Edge :=
  ⟨171539, 171372592019184065, 171374042348927662, 470479516074996, 470485208784114⟩

private theorem boundary_seed_171539_valid : Valid boundarySeed171539 :=
  (batch166539 boundary_seed_166539_valid).1

private def boundarySeed176539 : Edge :=
  ⟨176539, 176458855475595456, 176460348802168409, 476517386870567, 476523105582838⟩

private theorem boundary_seed_176539_valid : Valid boundarySeed176539 :=
  (batch171539 boundary_seed_171539_valid).1

private def k197Rows77 : List SignedPsiRow :=
  [⟨155556, 158749, 0⟩]

private theorem k197_rows77_checked :
    signedWalk (gcdStep 151539 158750) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows77)
        7211 boundarySeed151539 =
      true := by
  decide +kernel

private theorem k197_psi_row77 {r : SignedPsiRow} (hr : r ∈ k197Rows77) (ha : 151539 ≤ r.left + 1)
    (hb : r.right < 158750) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_151539_valid (by decide) (by decide) (by decide)
    k197_rows77_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 77. -/
public theorem psi_gaussian_k197_cell77 {x : ℝ} (hl : 155556 ≤ x) (hu : x ≤ 158749) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row77 (r := ⟨155556, 158749, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def k197Rows78 : List SignedPsiRow :=
  [⟨158856, 162083, -31000000000000⟩]

private theorem k197_rows78_checked :
    signedWalk (gcdStep 156539 162084) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows78)
        5545 boundarySeed156539 =
      true := by
  decide +kernel

private theorem k197_psi_row78 {r : SignedPsiRow} (hr : r ∈ k197Rows78) (ha : 156539 ≤ r.left + 1)
    (hb : r.right < 162084) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_156539_valid (by decide) (by decide) (by decide)
    k197_rows78_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 78. -/
public theorem psi_gaussian_k197_cell78 {x : ℝ} (hl : 158856 ≤ x) (hu : x ≤ 162083) :
    -31 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row78 (r := ⟨158856, 162083, -31000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows80 : List SignedPsiRow :=
  [⟨162190, 165452, -94000000000000⟩, ⟨165559, 167203, -166000000000000⟩]

private theorem k197_rows80_checked :
    signedWalk (gcdStep 161539 167204) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows80)
        5665 boundarySeed161539 =
      true := by
  decide +kernel

private theorem k197_psi_row80 {r : SignedPsiRow} (hr : r ∈ k197Rows80) (ha : 161539 ≤ r.left + 1)
    (hb : r.right < 167204) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_161539_valid (by decide) (by decide) (by decide)
    k197_rows80_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 79. -/
public theorem psi_gaussian_k197_cell79 {x : ℝ} (hl : 162190 ≤ x) (hu : x ≤ 165452) :
    -94 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row80 (r := ⟨162190, 165452, -94000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 80. -/
public theorem psi_gaussian_k197_cell80 {x : ℝ} (hl : 165559 ≤ x) (hu : x ≤ 167203) :
    -166 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row80 (r := ⟨165559, 167203, -166000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows83 : List SignedPsiRow :=
  [⟨167256, 168909, -213000000000000⟩, ⟨168962, 170624, -231000000000000⟩,
    ⟨170677, 172347, -179000000000000⟩]

private theorem k197_rows83_checked :
    signedWalk (gcdStep 166539 172348) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows83)
        5809 boundarySeed166539 =
      true := by
  decide +kernel

private theorem k197_psi_row83 {r : SignedPsiRow} (hr : r ∈ k197Rows83) (ha : 166539 ≤ r.left + 1)
    (hb : r.right < 172348) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_166539_valid (by decide) (by decide) (by decide)
    k197_rows83_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 81. -/
public theorem psi_gaussian_k197_cell81 {x : ℝ} (hl : 167256 ≤ x) (hu : x ≤ 168909) :
    -213 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row83 (r := ⟨167256, 168909, -213000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 82. -/
public theorem psi_gaussian_k197_cell82 {x : ℝ} (hl : 168962 ≤ x) (hu : x ≤ 170624) :
    -231 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row83 (r := ⟨168962, 170624, -231000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 83. -/
public theorem psi_gaussian_k197_cell83 {x : ℝ} (hl : 170677 ≤ x) (hu : x ≤ 172347) :
    -179 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row83 (r := ⟨170677, 172347, -179000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows86 : List SignedPsiRow :=
  [⟨172346, 174025, -177000000000000⟩, ⟨174132, 175820, -262000000000000⟩,
    ⟨175872, 177569, -242000000000000⟩]

private theorem k197_rows86_checked :
    signedWalk (gcdStep 171539 177570) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows86)
        6031 boundarySeed171539 =
      true := by
  decide +kernel

private theorem k197_psi_row86 {r : SignedPsiRow} (hr : r ∈ k197Rows86) (ha : 171539 ≤ r.left + 1)
    (hb : r.right < 177570) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_171539_valid (by decide) (by decide) (by decide)
    k197_rows86_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 84. -/
public theorem psi_gaussian_k197_cell84 {x : ℝ} (hl : 172346 ≤ x) (hu : x ≤ 174025) :
    -177 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row86 (r := ⟨172346, 174025, -177000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 85. -/
public theorem psi_gaussian_k197_cell85 {x : ℝ} (hl : 174132 ≤ x) (hu : x ≤ 175820) :
    -262 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row86 (r := ⟨174132, 175820, -262000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 86. -/
public theorem psi_gaussian_k197_cell86 {x : ℝ} (hl : 175872 ≤ x) (hu : x ≤ 177569) :
    -242 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row86 (r := ⟨175872, 177569, -242000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows88 : List SignedPsiRow :=
  [⟨177622, 179327, -209000000000000⟩, ⟨179326, 181039, -105000000000000⟩]

private theorem k197_rows88_checked :
    signedWalk (gcdStep 176539 181040) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows88)
        4501 boundarySeed176539 =
      true := by
  decide +kernel

private theorem k197_psi_row88 {r : SignedPsiRow} (hr : r ∈ k197Rows88) (ha : 176539 ≤ r.left + 1)
    (hb : r.right < 181040) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_176539_valid (by decide) (by decide) (by decide)
    k197_rows88_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 87. -/
public theorem psi_gaussian_k197_cell87 {x : ℝ} (hl : 177622 ≤ x) (hu : x ≤ 179327) :
    -209 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row88 (r := ⟨177622, 179327, -209000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 88. -/
public theorem psi_gaussian_k197_cell88 {x : ℝ} (hl : 179326 ≤ x) (hu : x ≤ 181039) :
    -105 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row88 (r := ⟨179326, 181039, -105000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
