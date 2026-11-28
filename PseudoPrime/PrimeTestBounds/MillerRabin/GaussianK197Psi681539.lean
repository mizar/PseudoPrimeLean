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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch681539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch686539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch691539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch696539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch701539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch706539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch711539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch716539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 681539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_681539 :
    Valid ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  exact h681539

private theorem seed_686539 :
    Valid ⟨686539, 686412368585099605, 686417547019080632, 920996545007128, 921008049638333⟩ :=
  (batch681539 seed_681539).1

private theorem seed_691539 :
    Valid ⟨691539, 691312311202672969, 691317524145104807, 927716763830316, 927728395365848⟩ :=
  (batch686539 seed_686539).1

private theorem seed_696539 :
    Valid ⟨696539, 696477191823668755, 696482419560906906, 927716763830316, 927728395365848⟩ :=
  (batch691539 seed_691539).1

private theorem seed_701539 :
    Valid ⟨701539, 701362245240628828, 701367519381235723, 927716763830316, 927728395365848⟩ :=
  (batch696539 seed_696539).1

private theorem seed_706539 :
    Valid ⟨706539, 706503475488883296, 706508802955717116, 938937610224217, 938949341719052⟩ :=
  (batch701539 seed_701539).1

private theorem seed_711539 :
    Valid ⟨711539, 711639544889051334, 711644881009029805, 942304906054199, 942316637549039⟩ :=
  (batch706539 seed_706539).1

private theorem seed_716539 :
    Valid ⟨716539, 716572739177339342, 716578109465859762, 942304906054199, 942316637549039⟩ :=
  (batch711539 seed_711539).1

private def rows681539 : List SignedPsiRow :=
  [⟨681539, 686539, -379000000000000⟩]

private theorem rows_681539_checked :
    signedWalk (gcdStep 681539 686540) (fun n ↦ signedRowFloor (-1000000000000000) n rows681539)
        5001 ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩ =
      true := by
  decide +kernel

private theorem row_681539 {r : SignedPsiRow} (hr : r ∈ rows681539) (ha : 681539 ≤ r.left + 1)
    (hb : r.right < 686540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_681539 (by decide) (by decide) (by decide) rows_681539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 133 in this batch. -/
public theorem psi_cell133_681539 {x : ℝ} (hl : 681539 ≤ x) (hu : x ≤ 686539) :
    -379 ≤ Chebyshev.psi x - x := by
  have h :=
    row_681539 (r := ⟨681539, 686539, -379000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows686539 : List SignedPsiRow :=
  [⟨686539, 691539, -379000000000000⟩]

private theorem rows_686539_checked :
    signedWalk (gcdStep 686539 691540) (fun n ↦ signedRowFloor (-1000000000000000) n rows686539)
        5001 ⟨686539, 686412368585099605, 686417547019080632, 920996545007128, 921008049638333⟩ =
      true := by
  decide +kernel

private theorem row_686539 {r : SignedPsiRow} (hr : r ∈ rows686539) (ha : 686539 ≤ r.left + 1)
    (hb : r.right < 691540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_686539 (by decide) (by decide) (by decide) rows_686539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 133 in this batch. -/
public theorem psi_cell133_686539 {x : ℝ} (hl : 686539 ≤ x) (hu : x ≤ 691539) :
    -379 ≤ Chebyshev.psi x - x := by
  have h :=
    row_686539 (r := ⟨686539, 691539, -379000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows691539 : List SignedPsiRow :=
  [⟨691539, 696539, -379000000000000⟩]

private theorem rows_691539_checked :
    signedWalk (gcdStep 691539 696540) (fun n ↦ signedRowFloor (-1000000000000000) n rows691539)
        5001 ⟨691539, 691312311202672969, 691317524145104807, 927716763830316, 927728395365848⟩ =
      true := by
  decide +kernel

private theorem row_691539 {r : SignedPsiRow} (hr : r ∈ rows691539) (ha : 691539 ≤ r.left + 1)
    (hb : r.right < 696540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_691539 (by decide) (by decide) (by decide) rows_691539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 133 in this batch. -/
public theorem psi_cell133_691539 {x : ℝ} (hl : 691539 ≤ x) (hu : x ≤ 696539) :
    -379 ≤ Chebyshev.psi x - x := by
  have h :=
    row_691539 (r := ⟨691539, 696539, -379000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows696539 : List SignedPsiRow :=
  [⟨696539, 700957, -379000000000000⟩, ⟨701397, 701539, -271000000000000⟩]

private theorem rows_696539_checked :
    signedWalk (gcdStep 696539 701540) (fun n ↦ signedRowFloor (-1000000000000000) n rows696539)
        5001 ⟨696539, 696477191823668755, 696482419560906906, 927716763830316, 927728395365848⟩ =
      true := by
  decide +kernel

private theorem row_696539 {r : SignedPsiRow} (hr : r ∈ rows696539) (ha : 696539 ≤ r.left + 1)
    (hb : r.right < 701540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_696539 (by decide) (by decide) (by decide) rows_696539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 133 in this batch. -/
public theorem psi_cell133_696539 {x : ℝ} (hl : 696539 ≤ x) (hu : x ≤ 700957) :
    -379 ≤ Chebyshev.psi x - x := by
  have h :=
    row_696539 (r := ⟨696539, 700957, -379000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_696539 {x : ℝ} (hl : 701397 ≤ x) (hu : x ≤ 701539) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_696539 (r := ⟨701397, 701539, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows701539 : List SignedPsiRow :=
  [⟨701539, 706539, -271000000000000⟩]

private theorem rows_701539_checked :
    signedWalk (gcdStep 701539 706540) (fun n ↦ signedRowFloor (-1000000000000000) n rows701539)
        5001 ⟨701539, 701362245240628828, 701367519381235723, 927716763830316, 927728395365848⟩ =
      true := by
  decide +kernel

private theorem row_701539 {r : SignedPsiRow} (hr : r ∈ rows701539) (ha : 701539 ≤ r.left + 1)
    (hb : r.right < 706540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_701539 (by decide) (by decide) (by decide) rows_701539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_701539 {x : ℝ} (hl : 701539 ≤ x) (hu : x ≤ 706539) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_701539 (r := ⟨701539, 706539, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows706539 : List SignedPsiRow :=
  [⟨706539, 711539, -271000000000000⟩]

private theorem rows_706539_checked :
    signedWalk (gcdStep 706539 711540) (fun n ↦ signedRowFloor (-1000000000000000) n rows706539)
        5001 ⟨706539, 706503475488883296, 706508802955717116, 938937610224217, 938949341719052⟩ =
      true := by
  decide +kernel

private theorem row_706539 {r : SignedPsiRow} (hr : r ∈ rows706539) (ha : 706539 ≤ r.left + 1)
    (hb : r.right < 711540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_706539 (by decide) (by decide) (by decide) rows_706539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_706539 {x : ℝ} (hl : 706539 ≤ x) (hu : x ≤ 711539) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_706539 (r := ⟨706539, 711539, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows711539 : List SignedPsiRow :=
  [⟨711539, 716539, -271000000000000⟩]

private theorem rows_711539_checked :
    signedWalk (gcdStep 711539 716540) (fun n ↦ signedRowFloor (-1000000000000000) n rows711539)
        5001 ⟨711539, 711639544889051334, 711644881009029805, 942304906054199, 942316637549039⟩ =
      true := by
  decide +kernel

private theorem row_711539 {r : SignedPsiRow} (hr : r ∈ rows711539) (ha : 711539 ≤ r.left + 1)
    (hb : r.right < 716540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_711539 (by decide) (by decide) (by decide) rows_711539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_711539 {x : ℝ} (hl : 711539 ≤ x) (hu : x ≤ 716539) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_711539 (r := ⟨711539, 716539, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows716539 : List SignedPsiRow :=
  [⟨716539, 721539, -271000000000000⟩]

private theorem rows_716539_checked :
    signedWalk (gcdStep 716539 721540) (fun n ↦ signedRowFloor (-1000000000000000) n rows716539)
        5001 ⟨716539, 716572739177339342, 716578109465859762, 942304906054199, 942316637549039⟩ =
      true := by
  decide +kernel

private theorem row_716539 {r : SignedPsiRow} (hr : r ∈ rows716539) (ha : 716539 ≤ r.left + 1)
    (hb : r.right < 721540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_716539 (by decide) (by decide) (by decide) rows_716539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_716539 {x : ℝ} (hl : 716539 ≤ x) (hu : x ≤ 721539) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_716539 (r := ⟨716539, 721539, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
