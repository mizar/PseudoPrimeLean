/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To321539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin321539To641539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin641539To681539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin681539To721539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin721539To761539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin761539To801539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin801539To841539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin841539To881539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin881539To921539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin921539To961539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch961539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch966539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch971539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch976539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch981539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch986539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 961539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_961539 :
    Valid ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  have h761539 := (joined721539To761539 h721539).1
  have h801539 := (joined761539To801539 h761539).1
  have h841539 := (joined801539To841539 h801539).1
  have h881539 := (joined841539To881539 h841539).1
  have h921539 := (joined881539To921539 h881539).1
  have h961539 := (joined921539To961539 h921539).1
  exact h961539

private theorem seed_966539 :
    Valid ⟨966539, 966566468497449366, 966573077998451939, 1088618862387204, 1088631673355392⟩ :=
  (batch961539 seed_961539).1

private theorem seed_971539 :
    Valid ⟨971539, 971597689847870591, 971604302142994180, 1088618862387204, 1088631673355392⟩ :=
  (batch966539 seed_966539).1

private theorem seed_976539 :
    Valid ⟨976539, 976603172512363965, 976609795810791725, 1088618862387204, 1088631673355392⟩ :=
  (batch971539 seed_971539).1

private theorem seed_981539 :
    Valid ⟨981539, 981348438476331104, 981355090621901309, 1088618862387204, 1088631673355392⟩ :=
  (batch976539 seed_976539).1

private theorem seed_986539 :
    Valid ⟨986539, 986240342261767815, 986247008254562085, 1095517575725254, 1095530504794266⟩ :=
  (batch981539 seed_981539).1

private def rows961539 : List SignedPsiRow :=
  [⟨961539, 966539, -272000000000000⟩]

private theorem rows_961539_checked :
    signedWalk (gcdStep 961539 966540) (fun n ↦ signedRowFloor (-1000000000000000) n rows961539)
        5001 ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩ =
      true := by
  decide +kernel

private theorem row_961539 {r : SignedPsiRow} (hr : r ∈ rows961539) (ha : 961539 ≤ r.left + 1)
    (hb : r.right < 966540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_961539 (by decide) (by decide) (by decide) rows_961539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_961539 {x : ℝ} (hl : 961539 ≤ x) (hu : x ≤ 966539) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_961539 (r := ⟨961539, 966539, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows966539 : List SignedPsiRow :=
  [⟨966539, 971539, -272000000000000⟩]

private theorem rows_966539_checked :
    signedWalk (gcdStep 966539 971540) (fun n ↦ signedRowFloor (-1000000000000000) n rows966539)
        5001 ⟨966539, 966566468497449366, 966573077998451939, 1088618862387204, 1088631673355392⟩ =
      true := by
  decide +kernel

private theorem row_966539 {r : SignedPsiRow} (hr : r ∈ rows966539) (ha : 966539 ≤ r.left + 1)
    (hb : r.right < 971540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_966539 (by decide) (by decide) (by decide) rows_966539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_966539 {x : ℝ} (hl : 966539 ≤ x) (hu : x ≤ 971539) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_966539 (r := ⟨966539, 971539, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows971539 : List SignedPsiRow :=
  [⟨971539, 974282, -272000000000000⟩, ⟨974725, 976539, -483000000000000⟩]

private theorem rows_971539_checked :
    signedWalk (gcdStep 971539 976540) (fun n ↦ signedRowFloor (-1000000000000000) n rows971539)
        5001 ⟨971539, 971597689847870591, 971604302142994180, 1088618862387204, 1088631673355392⟩ =
      true := by
  decide +kernel

private theorem row_971539 {r : SignedPsiRow} (hr : r ∈ rows971539) (ha : 971539 ≤ r.left + 1)
    (hb : r.right < 976540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_971539 (by decide) (by decide) (by decide) rows_971539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_971539 {x : ℝ} (hl : 971539 ≤ x) (hu : x ≤ 974282) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_971539 (r := ⟨971539, 974282, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 143 in this batch. -/
public theorem psi_cell143_971539 {x : ℝ} (hl : 974725 ≤ x) (hu : x ≤ 976539) :
    -483 ≤ Chebyshev.psi x - x := by
  have h :=
    row_971539 (r := ⟨974725, 976539, -483000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows976539 : List SignedPsiRow :=
  [⟨976539, 981539, -483000000000000⟩]

private theorem rows_976539_checked :
    signedWalk (gcdStep 976539 981540) (fun n ↦ signedRowFloor (-1000000000000000) n rows976539)
        5001 ⟨976539, 976603172512363965, 976609795810791725, 1088618862387204, 1088631673355392⟩ =
      true := by
  decide +kernel

private theorem row_976539 {r : SignedPsiRow} (hr : r ∈ rows976539) (ha : 976539 ≤ r.left + 1)
    (hb : r.right < 981540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_976539 (by decide) (by decide) (by decide) rows_976539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 143 in this batch. -/
public theorem psi_cell143_976539 {x : ℝ} (hl : 976539 ≤ x) (hu : x ≤ 981539) :
    -483 ≤ Chebyshev.psi x - x := by
  have h :=
    row_976539 (r := ⟨976539, 981539, -483000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows981539 : List SignedPsiRow :=
  [⟨981539, 986539, -483000000000000⟩]

private theorem rows_981539_checked :
    signedWalk (gcdStep 981539 986540) (fun n ↦ signedRowFloor (-1000000000000000) n rows981539)
        5001 ⟨981539, 981348438476331104, 981355090621901309, 1088618862387204, 1088631673355392⟩ =
      true := by
  decide +kernel

private theorem row_981539 {r : SignedPsiRow} (hr : r ∈ rows981539) (ha : 981539 ≤ r.left + 1)
    (hb : r.right < 986540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_981539 (by decide) (by decide) (by decide) rows_981539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 143 in this batch. -/
public theorem psi_cell143_981539 {x : ℝ} (hl : 981539 ≤ x) (hu : x ≤ 986539) :
    -483 ≤ Chebyshev.psi x - x := by
  have h :=
    row_981539 (r := ⟨981539, 986539, -483000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows986539 : List SignedPsiRow :=
  [⟨986539, 991007, -483000000000000⟩]

private theorem rows_986539_checked :
    signedWalk (gcdStep 986539 991540) (fun n ↦ signedRowFloor (-1000000000000000) n rows986539)
        5001 ⟨986539, 986240342261767815, 986247008254562085, 1095517575725254, 1095530504794266⟩ =
      true := by
  decide +kernel

private theorem row_986539 {r : SignedPsiRow} (hr : r ∈ rows986539) (ha : 986539 ≤ r.left + 1)
    (hb : r.right < 991540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_986539 (by decide) (by decide) (by decide) rows_986539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 143 in this batch. -/
public theorem psi_cell143_986539 {x : ℝ} (hl : 986539 ≤ x) (hu : x ≤ 991007) :
    -483 ≤ Chebyshev.psi x - x := by
  have h :=
    row_986539 (r := ⟨986539, 991007, -483000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
