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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch761539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch766539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch771539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch776539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch781539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch786539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch791539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch796539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 761539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_761539 :
    Valid ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  have h761539 := (joined721539To761539 h721539).1
  exact h761539

private theorem seed_766539 :
    Valid ⟨766539, 766515860919167815, 766521545846317146, 969323284128657, 969335329903535⟩ :=
  (batch761539 seed_761539).1

private theorem seed_771539 :
    Valid ⟨771539, 771564332433043628, 771570066296020882, 976099789998232, 976111948968637⟩ :=
  (batch766539 seed_766539).1

private theorem seed_776539 :
    Valid ⟨776539, 776411802478420273, 776417541711842328, 982880847623670, 982893007239747⟩ :=
  (batch771539 seed_771539).1

private theorem seed_781539 :
    Valid ⟨781539, 781532914755499894, 781538680576363060, 989664172811091, 989676338238130⟩ :=
  (batch776539 seed_776539).1

private theorem seed_786539 :
    Valid ⟨786539, 786473191412509356, 786479016874675260, 989664172811091, 989676338238130⟩ :=
  (batch781539 seed_781539).1

private theorem seed_791539 :
    Valid ⟨791539, 791531199979727438, 791537028115218617, 996452017626611, 996464214691058⟩ :=
  (batch786539 seed_786539).1

private theorem seed_796539 :
    Valid ⟨796539, 796625522429139383, 796631368640420656, 996452017626611, 996464214691058⟩ :=
  (batch791539 seed_791539).1

private def rows761539 : List SignedPsiRow :=
  [⟨761539, 766539, -396000000000000⟩]

private theorem rows_761539_checked :
    signedWalk (gcdStep 761539 766540) (fun n ↦ signedRowFloor (-1000000000000000) n rows761539)
        5001 ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩ =
      true := by
  decide +kernel

private theorem row_761539 {r : SignedPsiRow} (hr : r ∈ rows761539) (ha : 761539 ≤ r.left + 1)
    (hb : r.right < 766540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_761539 (by decide) (by decide) (by decide) rows_761539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_761539 {x : ℝ} (hl : 761539 ≤ x) (hu : x ≤ 766539) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_761539 (r := ⟨761539, 766539, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows766539 : List SignedPsiRow :=
  [⟨766539, 771539, -396000000000000⟩]

private theorem rows_766539_checked :
    signedWalk (gcdStep 766539 771540) (fun n ↦ signedRowFloor (-1000000000000000) n rows766539)
        5001 ⟨766539, 766515860919167815, 766521545846317146, 969323284128657, 969335329903535⟩ =
      true := by
  decide +kernel

private theorem row_766539 {r : SignedPsiRow} (hr : r ∈ rows766539) (ha : 766539 ≤ r.left + 1)
    (hb : r.right < 771540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_766539 (by decide) (by decide) (by decide) rows_766539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_766539 {x : ℝ} (hl : 766539 ≤ x) (hu : x ≤ 771539) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_766539 (r := ⟨766539, 771539, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows771539 : List SignedPsiRow :=
  [⟨771539, 776539, -396000000000000⟩]

private theorem rows_771539_checked :
    signedWalk (gcdStep 771539 776540) (fun n ↦ signedRowFloor (-1000000000000000) n rows771539)
        5001 ⟨771539, 771564332433043628, 771570066296020882, 976099789998232, 976111948968637⟩ =
      true := by
  decide +kernel

private theorem row_771539 {r : SignedPsiRow} (hr : r ∈ rows771539) (ha : 771539 ≤ r.left + 1)
    (hb : r.right < 776540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_771539 (by decide) (by decide) (by decide) rows_771539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_771539 {x : ℝ} (hl : 771539 ≤ x) (hu : x ≤ 776539) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_771539 (r := ⟨771539, 776539, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows776539 : List SignedPsiRow :=
  [⟨776539, 781539, -396000000000000⟩]

private theorem rows_776539_checked :
    signedWalk (gcdStep 776539 781540) (fun n ↦ signedRowFloor (-1000000000000000) n rows776539)
        5001 ⟨776539, 776411802478420273, 776417541711842328, 982880847623670, 982893007239747⟩ =
      true := by
  decide +kernel

private theorem row_776539 {r : SignedPsiRow} (hr : r ∈ rows776539) (ha : 776539 ≤ r.left + 1)
    (hb : r.right < 781540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_776539 (by decide) (by decide) (by decide) rows_776539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_776539 {x : ℝ} (hl : 776539 ≤ x) (hu : x ≤ 781539) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_776539 (r := ⟨776539, 781539, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows781539 : List SignedPsiRow :=
  [⟨781539, 786539, -396000000000000⟩]

private theorem rows_781539_checked :
    signedWalk (gcdStep 781539 786540) (fun n ↦ signedRowFloor (-1000000000000000) n rows781539)
        5001 ⟨781539, 781532914755499894, 781538680576363060, 989664172811091, 989676338238130⟩ =
      true := by
  decide +kernel

private theorem row_781539 {r : SignedPsiRow} (hr : r ∈ rows781539) (ha : 781539 ≤ r.left + 1)
    (hb : r.right < 786540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_781539 (by decide) (by decide) (by decide) rows_781539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_781539 {x : ℝ} (hl : 781539 ≤ x) (hu : x ≤ 786539) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_781539 (r := ⟨781539, 786539, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows786539 : List SignedPsiRow :=
  [⟨786539, 787078, -396000000000000⟩, ⟨787519, 791539, -103000000000000⟩]

private theorem rows_786539_checked :
    signedWalk (gcdStep 786539 791540) (fun n ↦ signedRowFloor (-1000000000000000) n rows786539)
        5001 ⟨786539, 786473191412509356, 786479016874675260, 989664172811091, 989676338238130⟩ =
      true := by
  decide +kernel

private theorem row_786539 {r : SignedPsiRow} (hr : r ∈ rows786539) (ha : 786539 ≤ r.left + 1)
    (hb : r.right < 791540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_786539 (by decide) (by decide) (by decide) rows_786539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_786539 {x : ℝ} (hl : 786539 ≤ x) (hu : x ≤ 787078) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_786539 (r := ⟨786539, 787078, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_786539 {x : ℝ} (hl : 787519 ≤ x) (hu : x ≤ 791539) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_786539 (r := ⟨787519, 791539, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows791539 : List SignedPsiRow :=
  [⟨791539, 796539, -103000000000000⟩]

private theorem rows_791539_checked :
    signedWalk (gcdStep 791539 796540) (fun n ↦ signedRowFloor (-1000000000000000) n rows791539)
        5001 ⟨791539, 791531199979727438, 791537028115218617, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_791539 {r : SignedPsiRow} (hr : r ∈ rows791539) (ha : 791539 ≤ r.left + 1)
    (hb : r.right < 796540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_791539 (by decide) (by decide) (by decide) rows_791539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_791539 {x : ℝ} (hl : 791539 ≤ x) (hu : x ≤ 796539) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_791539 (r := ⟨791539, 796539, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows796539 : List SignedPsiRow :=
  [⟨796539, 801539, -103000000000000⟩]

private theorem rows_796539_checked :
    signedWalk (gcdStep 796539 801540) (fun n ↦ signedRowFloor (-1000000000000000) n rows796539)
        5001 ⟨796539, 796625522429139383, 796631368640420656, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_796539 {r : SignedPsiRow} (hr : r ∈ rows796539) (ha : 796539 ≤ r.left + 1)
    (hb : r.right < 801540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_796539 (by decide) (by decide) (by decide) rows_796539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_796539 {x : ℝ} (hl : 796539 ≤ x) (hu : x ≤ 801539) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_796539 (r := ⟨796539, 801539, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
