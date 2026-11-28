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

/-! # Signed Chebyshev bounds for K197 cells 34 through 36 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def k197Seed36 : Edge :=
  ⟨116539, 116486170396305392, 116487141911824128, 387405952542179, 387410641104636⟩

private theorem k197_seed36_valid : Valid k197Seed36 :=
  (batch111539 (batch106539 bridge_start_valid).1).1

private def k197Rows36 : List SignedPsiRow :=
  [⟨116692, 116864, -128000000000000⟩, ⟨116876, 117220, -126000000000000⟩,
    ⟨117232, 117576, -124000000000000⟩]

private theorem k197_rows36_checked :
    signedWalk (gcdStep 116539 117577) (fun n ↦ signedRowFloor (-1000000000000000) n k197Rows36)
        1038 k197Seed36 =
      true := by
  decide +kernel

private theorem k197_psi_row36 {r : SignedPsiRow} (hr : r ∈ k197Rows36) (ha : 116539 ≤ r.left + 1)
    (hb : r.right < 117577) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr k197_seed36_valid (by decide) (by decide) (by decide) k197_rows36_checked ha
    hb hlt hl hu

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 34. -/
public theorem psi_gaussian_k197_cell34 {x : ℝ} (hl : 116692 ≤ x) (hu : x ≤ 116864) :
    -128 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row36 (r := ⟨116692, 116864, -128000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 35. -/
public theorem psi_gaussian_k197_cell35 {x : ℝ} (hl : 116876 ≤ x) (hu : x ≤ 117220) :
    -126 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row36 (r := ⟨116876, 117220, -126000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

/-- The signed Chebyshev boundary on the squared cutoff for K197 cell 36. -/
public theorem psi_gaussian_k197_cell36 {x : ℝ} (hl : 117232 ≤ x) (hu : x ≤ 117576) :
    -124 ≤ Chebyshev.psi x - x := by
  have h :=
    k197_psi_row36 (r := ⟨117232, 117576, -124000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
