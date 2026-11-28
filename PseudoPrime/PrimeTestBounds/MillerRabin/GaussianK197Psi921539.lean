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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch921539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch926539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch931539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch936539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch941539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch946539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch951539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch956539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 921539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_921539 :
    Valid ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  have h761539 := (joined721539To761539 h721539).1
  have h801539 := (joined761539To801539 h761539).1
  have h841539 := (joined801539To841539 h801539).1
  have h881539 := (joined841539To881539 h841539).1
  have h921539 := (joined881539To921539 h881539).1
  exact h921539

private theorem seed_926539 :
    Valid ⟨926539, 926922224503257658, 926928663976648094, 1061091242399709, 1061103934892325⟩ :=
  (batch921539 seed_921539).1

private theorem seed_931539 :
    Valid ⟨931539, 931718142652967269, 931724610039269399, 1061091242399709, 1061103934892325⟩ :=
  (batch926539 seed_926539).1

private theorem seed_936539 :
    Valid ⟨936539, 936770254416712369, 936776745537277321, 1067965440766627, 1067978159843455⟩ :=
  (batch931539 seed_931539).1

private theorem seed_941539 :
    Valid ⟨941539, 941762472428818080, 941768969632513838, 1067965440766627, 1067978159843455⟩ :=
  (batch936539 seed_936539).1

private theorem seed_946539 :
    Valid ⟨946539, 946694669996915947, 946701188663639853, 1074843766737711, 1074856551461252⟩ :=
  (batch941539 seed_941539).1

private theorem seed_951539 :
    Valid ⟨951539, 951635682335347026, 951642233310302761, 1074843766737711, 1074856551461252⟩ :=
  (batch946539 seed_946539).1

private theorem seed_956539 :
    Valid ⟨956539, 956516597372522837, 956523151516747531, 1081728253389386, 1081741038637830⟩ :=
  (batch951539 seed_951539).1

private def rows921539 : List SignedPsiRow :=
  [⟨921539, 926539, 0⟩]

private theorem rows_921539_checked :
    signedWalk (gcdStep 921539 926540) (fun n ↦ signedRowFloor (-1000000000000000) n rows921539)
        5001 ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩ =
      true := by
  decide +kernel

private theorem row_921539 {r : SignedPsiRow} (hr : r ∈ rows921539) (ha : 921539 ≤ r.left + 1)
    (hb : r.right < 926540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_921539 (by decide) (by decide) (by decide) rows_921539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_921539 {x : ℝ} (hl : 921539 ≤ x) (hu : x ≤ 926539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_921539 (r := ⟨921539, 926539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows926539 : List SignedPsiRow :=
  [⟨926539, 931539, 0⟩]

private theorem rows_926539_checked :
    signedWalk (gcdStep 926539 931540) (fun n ↦ signedRowFloor (-1000000000000000) n rows926539)
        5001 ⟨926539, 926922224503257658, 926928663976648094, 1061091242399709, 1061103934892325⟩ =
      true := by
  decide +kernel

private theorem row_926539 {r : SignedPsiRow} (hr : r ∈ rows926539) (ha : 926539 ≤ r.left + 1)
    (hb : r.right < 931540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_926539 (by decide) (by decide) (by decide) rows_926539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_926539 {x : ℝ} (hl : 926539 ≤ x) (hu : x ≤ 931539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_926539 (r := ⟨926539, 931539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows931539 : List SignedPsiRow :=
  [⟨931539, 936539, 0⟩]

private theorem rows_931539_checked :
    signedWalk (gcdStep 931539 936540) (fun n ↦ signedRowFloor (-1000000000000000) n rows931539)
        5001 ⟨931539, 931718142652967269, 931724610039269399, 1061091242399709, 1061103934892325⟩ =
      true := by
  decide +kernel

private theorem row_931539 {r : SignedPsiRow} (hr : r ∈ rows931539) (ha : 931539 ≤ r.left + 1)
    (hb : r.right < 936540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_931539 (by decide) (by decide) (by decide) rows_931539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_931539 {x : ℝ} (hl : 931539 ≤ x) (hu : x ≤ 936539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_931539 (r := ⟨931539, 936539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows936539 : List SignedPsiRow :=
  [⟨936539, 941539, 0⟩]

private theorem rows_936539_checked :
    signedWalk (gcdStep 936539 941540) (fun n ↦ signedRowFloor (-1000000000000000) n rows936539)
        5001 ⟨936539, 936770254416712369, 936776745537277321, 1067965440766627, 1067978159843455⟩ =
      true := by
  decide +kernel

private theorem row_936539 {r : SignedPsiRow} (hr : r ∈ rows936539) (ha : 936539 ≤ r.left + 1)
    (hb : r.right < 941540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_936539 (by decide) (by decide) (by decide) rows_936539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_936539 {x : ℝ} (hl : 936539 ≤ x) (hu : x ≤ 941539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_936539 (r := ⟨936539, 941539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows941539 : List SignedPsiRow :=
  [⟨941539, 941696, 0⟩, ⟨942138, 946539, -272000000000000⟩]

private theorem rows_941539_checked :
    signedWalk (gcdStep 941539 946540) (fun n ↦ signedRowFloor (-1000000000000000) n rows941539)
        5001 ⟨941539, 941762472428818080, 941768969632513838, 1067965440766627, 1067978159843455⟩ =
      true := by
  decide +kernel

private theorem row_941539 {r : SignedPsiRow} (hr : r ∈ rows941539) (ha : 941539 ≤ r.left + 1)
    (hb : r.right < 946540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_941539 (by decide) (by decide) (by decide) rows_941539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_941539 {x : ℝ} (hl : 941539 ≤ x) (hu : x ≤ 941696) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_941539 (r := ⟨941539, 941696, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_941539 {x : ℝ} (hl : 942138 ≤ x) (hu : x ≤ 946539) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_941539 (r := ⟨942138, 946539, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows946539 : List SignedPsiRow :=
  [⟨946539, 951539, -272000000000000⟩]

private theorem rows_946539_checked :
    signedWalk (gcdStep 946539 951540) (fun n ↦ signedRowFloor (-1000000000000000) n rows946539)
        5001 ⟨946539, 946694669996915947, 946701188663639853, 1074843766737711, 1074856551461252⟩ =
      true := by
  decide +kernel

private theorem row_946539 {r : SignedPsiRow} (hr : r ∈ rows946539) (ha : 946539 ≤ r.left + 1)
    (hb : r.right < 951540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_946539 (by decide) (by decide) (by decide) rows_946539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_946539 {x : ℝ} (hl : 946539 ≤ x) (hu : x ≤ 951539) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_946539 (r := ⟨946539, 951539, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows951539 : List SignedPsiRow :=
  [⟨951539, 956539, -272000000000000⟩]

private theorem rows_951539_checked :
    signedWalk (gcdStep 951539 956540) (fun n ↦ signedRowFloor (-1000000000000000) n rows951539)
        5001 ⟨951539, 951635682335347026, 951642233310302761, 1074843766737711, 1074856551461252⟩ =
      true := by
  decide +kernel

private theorem row_951539 {r : SignedPsiRow} (hr : r ∈ rows951539) (ha : 951539 ≤ r.left + 1)
    (hb : r.right < 956540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_951539 (by decide) (by decide) (by decide) rows_951539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_951539 {x : ℝ} (hl : 951539 ≤ x) (hu : x ≤ 956539) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_951539 (r := ⟨951539, 956539, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows956539 : List SignedPsiRow :=
  [⟨956539, 961539, -272000000000000⟩]

private theorem rows_956539_checked :
    signedWalk (gcdStep 956539 961540) (fun n ↦ signedRowFloor (-1000000000000000) n rows956539)
        5001 ⟨956539, 956516597372522837, 956523151516747531, 1081728253389386, 1081741038637830⟩ =
      true := by
  decide +kernel

private theorem row_956539 {r : SignedPsiRow} (hr : r ∈ rows956539) (ha : 956539 ≤ r.left + 1)
    (hb : r.right < 961540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_956539 (by decide) (by decide) (by decide) rows_956539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 142 in this batch. -/
public theorem psi_cell142_956539 {x : ℝ} (hl : 956539 ≤ x) (hu : x ≤ 961539) :
    -272 ≤ Chebyshev.psi x - x := by
  have h :=
    row_956539 (r := ⟨956539, 961539, -272000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
