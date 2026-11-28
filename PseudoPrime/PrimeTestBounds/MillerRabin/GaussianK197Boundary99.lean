/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Boundary88
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch176539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch181539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch186539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch191539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch196539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch201539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch206539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch211539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed Chebyshev bounds for K197 cells 89 through 99 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def boundarySeed181539 : Edge :=
  ⟨181539, 181400821236517595, 181402347797528581, 483658631419302, 483664422362539⟩

private theorem boundary_seed_181539_valid : Valid boundarySeed181539 :=
  (batch176539 boundary_seed_176539_valid).1

private def boundarySeed186539 : Edge :=
  ⟨186539, 186559095622921103, 186560655391780817, 489724738027783, 489730665251735⟩

private theorem boundary_seed_186539_valid : Valid boundarySeed186539 :=
  (batch181539 boundary_seed_181539_valid).1

private def boundarySeed191539 : Edge :=
  ⟨191539, 191558662826644864, 191560257013900818, 495795475751650, 495801405654795⟩

private theorem boundary_seed_191539_valid : Valid boundarySeed191539 :=
  (batch186539 boundary_seed_186539_valid).1

private def boundarySeed196539 : Edge :=
  ⟨196539, 196526302637460001, 196527934662644933, 507973543428502, 507979627855476⟩

private theorem boundary_seed_196539_valid : Valid boundarySeed196539 :=
  (batch191539 boundary_seed_191539_valid).1

private def boundarySeed201539 : Edge :=
  ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩

private theorem boundary_seed_201539_valid : Valid boundarySeed201539 :=
  (batch196539 boundary_seed_196539_valid).1

private def boundarySeed206539 : Edge :=
  ⟨206539, 206527250279922435, 206528931783278320, 518158103756435, 518164190674656⟩

private theorem boundary_seed_206539_valid : Valid boundarySeed206539 :=
  (batch201539 boundary_seed_201539_valid).1

private def boundarySeed211539 : Edge :=
  ⟨211539, 211690773014747110, 211692481446359927, 524282787143811, 524288876466628⟩

private theorem boundary_seed_211539_valid : Valid boundarySeed211539 :=
  (batch206539 boundary_seed_206539_valid).1

private def boundarySeed216539 : Edge :=
  ⟨216539, 216465261081056162, 216466996017106148, 536553910612930, 536560177875132⟩

private theorem boundary_seed_216539_valid : Valid boundarySeed216539 :=
  (batch211539 boundary_seed_211539_valid).1

private def k197Rows89 : List SignedPsiRow :=
  [⟨181146, 184598, -190000000000000⟩]

private theorem k197_rows89_checked :
    signedWalk (gcdStep 176539 184599) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows89)
        8060 boundarySeed176539 =
      true := by
  decide +kernel

private theorem k197_psi_row89 {r : SignedPsiRow} (hr : r ∈ k197Rows89) (ha : 176539 ≤ r.left + 1)
    (hb : r.right < 184599) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_176539_valid (by decide) (by decide) (by decide)
    k197_rows89_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 89. -/
public theorem psi_gaussian_k197_cell89 {x : ℝ} (hl : 181146 ≤ x) (hu : x ≤ 184598) :
    -190 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row89 (r := ⟨181146, 184598, -190000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows90 : List SignedPsiRow :=
  [⟨184705, 188192, -107000000000000⟩]

private theorem k197_rows90_checked :
    signedWalk (gcdStep 181539 188193) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows90)
        6654 boundarySeed181539 =
      true := by
  decide +kernel

private theorem k197_psi_row90 {r : SignedPsiRow} (hr : r ∈ k197Rows90) (ha : 181539 ≤ r.left + 1)
    (hb : r.right < 188193) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_181539_valid (by decide) (by decide) (by decide)
    k197_rows90_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 90. -/
public theorem psi_gaussian_k197_cell90 {x : ℝ} (hl : 184705 ≤ x) (hu : x ≤ 188192) :
    -107 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row90 (r := ⟨184705, 188192, -107000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows91 : List SignedPsiRow :=
  [⟨188299, 191820, -77000000000000⟩]

private theorem k197_rows91_checked :
    signedWalk (gcdStep 186539 191821) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows91)
        5282 boundarySeed186539 =
      true := by
  decide +kernel

private theorem k197_psi_row91 {r : SignedPsiRow} (hr : r ∈ k197Rows91) (ha : 186539 ≤ r.left + 1)
    (hb : r.right < 191821) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_186539_valid (by decide) (by decide) (by decide)
    k197_rows91_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 91. -/
public theorem psi_gaussian_k197_cell91 {x : ℝ} (hl : 188299 ≤ x) (hu : x ≤ 191820) :
    -77 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row91 (r := ⟨188299, 191820, -77000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows93 : List SignedPsiRow :=
  [⟨191927, 195483, -40000000000000⟩, ⟨195590, 199180, -39000000000000⟩]

private theorem k197_rows93_checked :
    signedWalk (gcdStep 191539 199181) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows93)
        7642 boundarySeed191539 =
      true := by
  decide +kernel

private theorem k197_psi_row93 {r : SignedPsiRow} (hr : r ∈ k197Rows93) (ha : 191539 ≤ r.left + 1)
    (hb : r.right < 199181) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_191539_valid (by decide) (by decide) (by decide)
    k197_rows93_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 92. -/
public theorem psi_gaussian_k197_cell92 {x : ℝ} (hl : 191927 ≤ x) (hu : x ≤ 195483) :
    -40 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row93 (r := ⟨191927, 195483, -40000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 93. -/
public theorem psi_gaussian_k197_cell93 {x : ℝ} (hl : 195590 ≤ x) (hu : x ≤ 199180) :
    -39 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row93 (r := ⟨195590, 199180, -39000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows94 : List SignedPsiRow :=
  [⟨199287, 202912, -97000000000000⟩]

private theorem k197_rows94_checked :
    signedWalk (gcdStep 196539 202913) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows94)
        6374 boundarySeed196539 =
      true := by
  decide +kernel

private theorem k197_psi_row94 {r : SignedPsiRow} (hr : r ∈ k197Rows94) (ha : 196539 ≤ r.left + 1)
    (hb : r.right < 202913) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_196539_valid (by decide) (by decide) (by decide)
    k197_rows94_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 94. -/
public theorem psi_gaussian_k197_cell94 {x : ℝ} (hl : 199287 ≤ x) (hu : x ≤ 202912) :
    -97 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row94 (r := ⟨199287, 202912, -97000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows95 : List SignedPsiRow :=
  [⟨203019, 206679, -144000000000000⟩]

private theorem k197_rows95_checked :
    signedWalk (gcdStep 201539 206680) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows95)
        5141 boundarySeed201539 =
      true := by
  decide +kernel

private theorem k197_psi_row95 {r : SignedPsiRow} (hr : r ∈ k197Rows95) (ha : 201539 ≤ r.left + 1)
    (hb : r.right < 206680) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_201539_valid (by decide) (by decide) (by decide)
    k197_rows95_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 95. -/
public theorem psi_gaussian_k197_cell95 {x : ℝ} (hl : 203019 ≤ x) (hu : x ≤ 206679) :
    -144 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row95 (r := ⟨203019, 206679, -144000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows97 : List SignedPsiRow :=
  [⟨206786, 210480, -109000000000000⟩, ⟨210587, 214316, 0⟩]

private theorem k197_rows97_checked :
    signedWalk (gcdStep 206539 214317) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows97)
        7778 boundarySeed206539 =
      true := by
  decide +kernel

private theorem k197_psi_row97 {r : SignedPsiRow} (hr : r ∈ k197Rows97) (ha : 206539 ≤ r.left + 1)
    (hb : r.right < 214317) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_206539_valid (by decide) (by decide) (by decide)
    k197_rows97_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 96. -/
public theorem psi_gaussian_k197_cell96 {x : ℝ} (hl : 206786 ≤ x) (hu : x ≤ 210480) :
    -109 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row97 (r := ⟨206786, 210480, -109000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 97. -/
public theorem psi_gaussian_k197_cell97 {x : ℝ} (hl : 210587 ≤ x) (hu : x ≤ 214316) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row97 (r := ⟨210587, 214316, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  simpa only [Int.cast_zero, zero_div] using h

private def k197Rows98 : List SignedPsiRow :=
  [⟨214423, 218186, -105000000000000⟩]

private theorem k197_rows98_checked :
    signedWalk (gcdStep 211539 218187) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows98)
        6648 boundarySeed211539 =
      true := by
  decide +kernel

private theorem k197_psi_row98 {r : SignedPsiRow} (hr : r ∈ k197Rows98) (ha : 211539 ≤ r.left + 1)
    (hb : r.right < 218187) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_211539_valid (by decide) (by decide) (by decide)
    k197_rows98_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 98. -/
public theorem psi_gaussian_k197_cell98 {x : ℝ} (hl : 214423 ≤ x) (hu : x ≤ 218186) :
    -105 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row98 (r := ⟨214423, 218186, -105000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

private def k197Rows99 : List SignedPsiRow :=
  [⟨218293, 222091, -141000000000000⟩]

private theorem k197_rows99_checked :
    signedWalk (gcdStep 216539 222092) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows99)
        5553 boundarySeed216539 =
      true := by
  decide +kernel

private theorem k197_psi_row99 {r : SignedPsiRow} (hr : r ∈ k197Rows99) (ha : 216539 ≤ r.left + 1)
    (hb : r.right < 222092) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr boundary_seed_216539_valid (by decide) (by decide) (by decide)
    k197_rows99_checked ha hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 99. -/
public theorem psi_gaussian_k197_cell99 {x : ℝ} (hl : 218293 ≤ x) (hu : x ≤ 222091) :
    -141 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row99 (r := ⟨218293, 222091, -141000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
