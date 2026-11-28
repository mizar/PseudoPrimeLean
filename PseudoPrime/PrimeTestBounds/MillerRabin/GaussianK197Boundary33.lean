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

/-! # Signed Chebyshev boundaries for K197 cells 11 through 33 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def k197Seed : Edge :=
  ⟨111539, 111484944561403024, 111485890653785676, 381585869620603, 381590553754195⟩

private theorem k197_seed_valid : Valid k197Seed :=
  (batch106539 bridge_start_valid).1

private def k197Rows : List SignedPsiRow :=
  [⟨112909, 113078, -115000000000000⟩, ⟨113084, 113422, -58000000000000⟩,
    ⟨113434, 113604, -43000000000000⟩, ⟨113610, 113779, -98000000000000⟩,
    ⟨113778, 113948, -98000000000000⟩, ⟨113960, 114300, -85000000000000⟩,
    ⟨114312, 114482, -115000000000000⟩, ⟨114488, 114574, -137000000000000⟩,
    ⟨114576, 114662, -136000000000000⟩, ⟨114664, 114835, -111000000000000⟩,
    ⟨114840, 115011, -120000000000000⟩, ⟨115017, 115187, -124000000000000⟩,
    ⟨115193, 115364, -133000000000000⟩, ⟨115370, 115456, -125000000000000⟩,
    ⟨115458, 115544, -143000000000000⟩, ⟨115543, 115587, -146000000000000⟩,
    ⟨115547, 115587, -141000000000000⟩, ⟨115586, 115629, -141000000000000⟩,
    ⟨115635, 115721, -145000000000000⟩, ⟨115720, 115764, -151000000000000⟩,
    ⟨115727, 115764, -145000000000000⟩, ⟨115763, 115806, -123000000000000⟩,
    ⟨115812, 116154, -84000000000000⟩, ⟨116166, 116509, -80000000000000⟩,
    ⟨116521, 116693, -114000000000000⟩]

set_option maxRecDepth 16384 in
-- The block reuses the certified incoming prefix and checks its overlapping rows together.
private theorem k197_rows_checked :
    signedWalk (gcdStep 111539 116694) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows) 5155
        k197Seed =
      true := by
  decide +kernel

private theorem k197_psi_row {r : SignedPsiRow} (hr : r ∈ k197Rows) (ha : 111539 ≤ r.left + 1)
    (hb : r.right < 116694) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed_valid (by decide) (by decide) (by decide) k197_rows_checked ha hb
    hlt hl hu

/-- Signed psi floor on the squared cutoff for compressed K197 cell 11. -/
public theorem psi_gaussian_k197_cell11 {x : ℝ} (hl : 112909 ≤ x) (hu : x ≤ 113078) :
    -115 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨112909, 113078, -115000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 12. -/
public theorem psi_gaussian_k197_cell12 {x : ℝ} (hl : 113084 ≤ x) (hu : x ≤ 113422) :
    -58 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨113084, 113422, -58000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 13. -/
public theorem psi_gaussian_k197_cell13 {x : ℝ} (hl : 113434 ≤ x) (hu : x ≤ 113604) :
    -43 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨113434, 113604, -43000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 14. -/
public theorem psi_gaussian_k197_cell14 {x : ℝ} (hl : 113610 ≤ x) (hu : x ≤ 113779) :
    -98 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨113610, 113779, -98000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 15. -/
public theorem psi_gaussian_k197_cell15 {x : ℝ} (hl : 113778 ≤ x) (hu : x ≤ 113948) :
    -98 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨113778, 113948, -98000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 16. -/
public theorem psi_gaussian_k197_cell16 {x : ℝ} (hl : 113960 ≤ x) (hu : x ≤ 114300) :
    -85 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨113960, 114300, -85000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 17. -/
public theorem psi_gaussian_k197_cell17 {x : ℝ} (hl : 114312 ≤ x) (hu : x ≤ 114482) :
    -115 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨114312, 114482, -115000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 18. -/
public theorem psi_gaussian_k197_cell18 {x : ℝ} (hl : 114488 ≤ x) (hu : x ≤ 114574) :
    -137 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨114488, 114574, -137000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 19. -/
public theorem psi_gaussian_k197_cell19 {x : ℝ} (hl : 114576 ≤ x) (hu : x ≤ 114662) :
    -136 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨114576, 114662, -136000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 20. -/
public theorem psi_gaussian_k197_cell20 {x : ℝ} (hl : 114664 ≤ x) (hu : x ≤ 114835) :
    -111 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨114664, 114835, -111000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 21. -/
public theorem psi_gaussian_k197_cell21 {x : ℝ} (hl : 114840 ≤ x) (hu : x ≤ 115011) :
    -120 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨114840, 115011, -120000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 22. -/
public theorem psi_gaussian_k197_cell22 {x : ℝ} (hl : 115017 ≤ x) (hu : x ≤ 115187) :
    -124 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115017, 115187, -124000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 23. -/
public theorem psi_gaussian_k197_cell23 {x : ℝ} (hl : 115193 ≤ x) (hu : x ≤ 115364) :
    -133 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115193, 115364, -133000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 24. -/
public theorem psi_gaussian_k197_cell24 {x : ℝ} (hl : 115370 ≤ x) (hu : x ≤ 115456) :
    -125 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115370, 115456, -125000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 25. -/
public theorem psi_gaussian_k197_cell25 {x : ℝ} (hl : 115458 ≤ x) (hu : x ≤ 115544) :
    -143 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115458, 115544, -143000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 26. -/
public theorem psi_gaussian_k197_cell26 {x : ℝ} (hl : 115543 ≤ x) (hu : x ≤ 115587) :
    -146 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115543, 115587, -146000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- After the prime at 115547, the signed floor on the rest of cell 26 is -141. -/
public theorem psi_gaussian_k197_cell26_right {x : ℝ} (hl : 115547 ≤ x) (hu : x ≤ 115587) :
    -141 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115547, 115587, -141000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 27. -/
public theorem psi_gaussian_k197_cell27 {x : ℝ} (hl : 115586 ≤ x) (hu : x ≤ 115629) :
    -141 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115586, 115629, -141000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 28. -/
public theorem psi_gaussian_k197_cell28 {x : ℝ} (hl : 115635 ≤ x) (hu : x ≤ 115721) :
    -145 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115635, 115721, -145000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 29. -/
public theorem psi_gaussian_k197_cell29 {x : ℝ} (hl : 115720 ≤ x) (hu : x ≤ 115764) :
    -151 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115720, 115764, -151000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed floor on the right part of K197 cell 29 is -145. -/
public theorem psi_gaussian_k197_cell29_right {x : ℝ} (hl : 115727 ≤ x) (hu : x ≤ 115764) :
    -145 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115727, 115764, -145000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 30. -/
public theorem psi_gaussian_k197_cell30 {x : ℝ} (hl : 115763 ≤ x) (hu : x ≤ 115806) :
    -123 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115763, 115806, -123000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 31. -/
public theorem psi_gaussian_k197_cell31 {x : ℝ} (hl : 115812 ≤ x) (hu : x ≤ 116154) :
    -84 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨115812, 116154, -84000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 32. -/
public theorem psi_gaussian_k197_cell32 {x : ℝ} (hl : 116166 ≤ x) (hu : x ≤ 116509) :
    -80 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨116166, 116509, -80000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- Signed psi floor on the squared cutoff for compressed K197 cell 33. -/
public theorem psi_gaussian_k197_cell33 {x : ℝ} (hl : 116521 ≤ x) (hu : x ≤ 116693) :
    -114 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row (r := ⟨116521, 116693, -114000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Abel boundary cost on compressed K197 cell 11. -/
public theorem gaussian_k197_cell11_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1343 / 2) 672) :
    let y := (1000805577377 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.130 := by
  apply
    k197_boundary_from_row (s := 1000805577377 / 1000000000000) (A := 112909) (B := 113078) (e :=
      115) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell11 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 12. -/
public theorem gaussian_k197_cell12_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 672 673) :
    let y := (8006680201 / 8000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.066 := by
  apply
    k197_boundary_from_row (s := 8006680201 / 8000000000) (A := 113084) (B := 113422) (e := 58)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell12 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 13. -/
public theorem gaussian_k197_cell13_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 673 (1347 / 2)) :
    let y := (500446893623 / 500000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.049 := by
  apply
    k197_boundary_from_row (s := 500446893623 / 500000000000) (A := 113434) (B := 113604) (e := 43)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell13 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 14. -/
public theorem gaussian_k197_cell14_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1347 / 2) 674) :
    let y := (50046155091 / 50000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.111 := by
  apply
    k197_boundary_from_row (s := 50046155091 / 50000000000) (A := 113610) (B := 113779) (e := 98)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell14 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 15. -/
public theorem gaussian_k197_cell15_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 674 (1349 / 2)) :
    let y := (50046155091 / 50000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.111 := by
  apply
    k197_boundary_from_row (s := 50046155091 / 50000000000) (A := 113778) (B := 113948) (e := 98)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell15 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 16. -/
public theorem gaussian_k197_cell16_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1349 / 2) (1351 / 2)) :
    let y := (1000981598501 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.096 := by
  apply
    k197_boundary_from_row (s := 1000981598501 / 1000000000000) (A := 113960) (B := 114300) (e :=
      85) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell16 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 17. -/
public theorem gaussian_k197_cell17_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1351 / 2) 676) :
    let y := (125129989903 / 125000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.130 := by
  apply
    k197_boundary_from_row (s := 125129989903 / 125000000000) (A := 114312) (B := 114482) (e := 115)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell17 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 18. -/
public theorem gaussian_k197_cell18_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 676 (2705 / 4)) :
    let y := (1001069013851 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.155 := by
  apply
    k197_boundary_from_row (s := 1001069013851 / 1000000000000) (A := 114488) (B := 114574) (e :=
      137) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell18 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 19. -/
public theorem gaussian_k197_cell19_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2705 / 4) (1353 / 2)) :
    let y := (1001083544773 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.153 := by
  apply
    k197_boundary_from_row (s := 1001083544773 / 1000000000000) (A := 114576) (B := 114662) (e :=
      136) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell19 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 20. -/
public theorem gaussian_k197_cell20_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1353 / 2) 677) :
    let y := (200219612957 / 200000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.125 := by
  apply
    k197_boundary_from_row (s := 200219612957 / 200000000000) (A := 114664) (B := 114835) (e := 111)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell20 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 21. -/
public theorem gaussian_k197_cell21_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 677 (1355 / 2)) :
    let y := (7821305251 / 7812500000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.135 := by
  apply
    k197_boundary_from_row (s := 7821305251 / 7812500000) (A := 114840) (B := 115011) (e := 120)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell21 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 22. -/
public theorem gaussian_k197_cell22_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1355 / 2) 678) :
    let y := (125144504497 / 125000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.140 := by
  apply
    k197_boundary_from_row (s := 125144504497 / 125000000000) (A := 115017) (B := 115187) (e := 124)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell22 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 23. -/
public theorem gaussian_k197_cell23_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 678 (1357 / 2)) :
    let y := (1001184956427 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.150 := by
  apply
    k197_boundary_from_row (s := 1001184956427 / 1000000000000) (A := 115193) (B := 115364) (e :=
      133) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell23 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 24. -/
public theorem gaussian_k197_cell24_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1357 / 2) (2715 / 4)) :
    let y := (1001213833581 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.141 := by
  apply
    k197_boundary_from_row (s := 1001213833581 / 1000000000000) (A := 115370) (B := 115456) (e :=
      125) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell24 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 25. -/
public theorem gaussian_k197_cell25_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2715 / 4) 679) :
    let y := (1001228255951 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.161 := by
  apply
    k197_boundary_from_row (s := 1001228255951 / 1000000000000) (A := 115458) (B := 115544) (e :=
      143) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell25 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 26. -/
public theorem gaussian_k197_cell26_boundary_le {L : ℝ} (hL : L ∈ Set.Icc 679 (5433 / 8)) :
    let y := (1001228255951 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.165 := by
  apply
    k197_boundary_from_row (s := 1001228255951 / 1000000000000) (A := 115543) (B := 115587) (e :=
      146) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell26 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 27. -/
public theorem gaussian_k197_cell27_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (5433 / 8) (2717 / 4)) :
    let y := (1001228255951 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.159 := by
  apply
    k197_boundary_from_row (s := 1001228255951 / 1000000000000) (A := 115586) (B := 115629) (e :=
      141) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell27 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 28. -/
public theorem gaussian_k197_cell28_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2717 / 4) (1359 / 2)) :
    let y := (50062853417 / 50000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.164 := by
  apply
    k197_boundary_from_row (s := 50062853417 / 50000000000) (A := 115635) (B := 115721) (e := 145)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell28 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 29. -/
public theorem gaussian_k197_cell29_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (1359 / 2) (5437 / 8)) :
    let y := (50062853417 / 50000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.170 := by
  apply
    k197_boundary_from_row (s := 50062853417 / 50000000000) (A := 115720) (B := 115764) (e := 151)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell29 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 30. -/
public theorem gaussian_k197_cell30_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (5437 / 8) (2719 / 4)) :
    let y := (50062853417 / 50000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.139 := by
  apply
    k197_boundary_from_row (s := 50062853417 / 50000000000) (A := 115763) (B := 115806) (e := 123)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell30 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 31. -/
public theorem gaussian_k197_cell31_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2719 / 4) (2723 / 4)) :
    let y := (500642918837 / 500000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.095 := by
  apply
    k197_boundary_from_row (s := 500642918837 / 500000000000) (A := 115812) (B := 116154) (e := 84)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell31 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 32. -/
public theorem gaussian_k197_cell32_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2723 / 4) (2727 / 4)) :
    let y := (250335811891 / 250000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.090 := by
  apply
    k197_boundary_from_row (s := 250335811891 / 250000000000) (A := 116166) (B := 116509) (e := 80)
      (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell32 hl hu)
      (by norm_num only)

/-- Abel boundary cost on compressed K197 cell 33. -/
public theorem gaussian_k197_cell33_boundary_le {L : ℝ} (hL : L ∈ Set.Icc (2727 / 4) (2729 / 4)) :
    let y := (1001400486393 / 1000000000000 : ℝ) * L / 2
    (-4 : ℝ) * (Chebyshev.psi (y ^ 2) - y ^ 2) * quarterWeight656 (y ^ 2) (y ^ 2) ≤ 0.129 := by
  apply
    k197_boundary_from_row (s := 1001400486393 / 1000000000000) (A := 116521) (B := 116693) (e :=
      114) (by norm_num only) (by norm_num only) hL (by norm_num only) (by norm_num only)
      (by norm_num only)
      (fun _ hl hu ↦ AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_gaussian_k197_cell33 hl hu)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
