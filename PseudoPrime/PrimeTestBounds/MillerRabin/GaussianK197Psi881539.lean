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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch881539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch886539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch891539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch896539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch901539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch906539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch911539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch916539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 881539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_881539 :
    Valid ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  have h761539 := (joined721539To761539 h721539).1
  have h801539 := (joined761539To801539 h761539).1
  have h841539 := (joined801539To841539 h801539).1
  have h881539 := (joined841539To881539 h841539).1
  exact h881539

private theorem seed_886539 :
    Valid ⟨886539, 886818139254799858, 886824436236879330, 1039369630891237, 1039382218633003⟩ :=
  (batch881539 seed_881539).1

private theorem seed_891539 :
    Valid ⟨891539, 891694581140459969, 891700882763878255, 1039369630891237, 1039382218633003⟩ :=
  (batch886539 seed_886539).1

private theorem seed_896539 :
    Valid ⟨896539, 896805970329026330, 896812292898368999, 1039369630891237, 1039382218633003⟩ :=
  (batch891539 seed_891539).1

private theorem seed_901539 :
    Valid ⟨901539, 901720685380952995, 901727049257808867, 1046222929973740, 1046235522765251⟩ :=
  (batch896539 seed_896539).1

private theorem seed_906539 :
    Valid ⟨906539, 906603126071419620, 906609492378114731, 1046222929973740, 1046235522765251⟩ :=
  (batch901539 seed_901539).1

private theorem seed_911539 :
    Valid ⟨911539, 911892214537799288, 911898596014063683, 1053082544590572, 1053095182829703⟩ :=
  (batch906539 seed_906539).1

private theorem seed_916539 :
    Valid ⟨916539, 916673325082273885, 916679743113070684, 1057657255195228, 1057669947687839⟩ :=
  (batch911539 seed_911539).1

private def rows881539 : List SignedPsiRow :=
  [⟨881539, 886539, -119000000000000⟩]

private theorem rows_881539_checked :
    signedWalk (gcdStep 881539 886540) (fun n ↦ signedRowFloor (-1000000000000000) n rows881539)
        5001 ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩ =
      true := by
  decide +kernel

private theorem row_881539 {r : SignedPsiRow} (hr : r ∈ rows881539) (ha : 881539 ≤ r.left + 1)
    (hb : r.right < 886540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_881539 (by decide) (by decide) (by decide) rows_881539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_881539 {x : ℝ} (hl : 881539 ≤ x) (hu : x ≤ 886539) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_881539 (r := ⟨881539, 886539, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows886539 : List SignedPsiRow :=
  [⟨886539, 891539, -119000000000000⟩]

private theorem rows_886539_checked :
    signedWalk (gcdStep 886539 891540) (fun n ↦ signedRowFloor (-1000000000000000) n rows886539)
        5001 ⟨886539, 886818139254799858, 886824436236879330, 1039369630891237, 1039382218633003⟩ =
      true := by
  decide +kernel

private theorem row_886539 {r : SignedPsiRow} (hr : r ∈ rows886539) (ha : 886539 ≤ r.left + 1)
    (hb : r.right < 891540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_886539 (by decide) (by decide) (by decide) rows_886539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_886539 {x : ℝ} (hl : 886539 ≤ x) (hu : x ≤ 891539) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_886539 (r := ⟨886539, 891539, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows891539 : List SignedPsiRow :=
  [⟨891539, 896539, -119000000000000⟩]

private theorem rows_891539_checked :
    signedWalk (gcdStep 891539 896540) (fun n ↦ signedRowFloor (-1000000000000000) n rows891539)
        5001 ⟨891539, 891694581140459969, 891700882763878255, 1039369630891237, 1039382218633003⟩ =
      true := by
  decide +kernel

private theorem row_891539 {r : SignedPsiRow} (hr : r ∈ rows891539) (ha : 891539 ≤ r.left + 1)
    (hb : r.right < 896540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_891539 (by decide) (by decide) (by decide) rows_891539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_891539 {x : ℝ} (hl : 891539 ≤ x) (hu : x ≤ 896539) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_891539 (r := ⟨891539, 896539, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows896539 : List SignedPsiRow :=
  [⟨896539, 901539, -119000000000000⟩]

private theorem rows_896539_checked :
    signedWalk (gcdStep 896539 901540) (fun n ↦ signedRowFloor (-1000000000000000) n rows896539)
        5001 ⟨896539, 896805970329026330, 896812292898368999, 1039369630891237, 1039382218633003⟩ =
      true := by
  decide +kernel

private theorem row_896539 {r : SignedPsiRow} (hr : r ∈ rows896539) (ha : 896539 ≤ r.left + 1)
    (hb : r.right < 901540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_896539 (by decide) (by decide) (by decide) rows_896539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_896539 {x : ℝ} (hl : 896539 ≤ x) (hu : x ≤ 901539) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_896539 (r := ⟨896539, 901539, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows901539 : List SignedPsiRow :=
  [⟨901539, 906539, -119000000000000⟩]

private theorem rows_901539_checked :
    signedWalk (gcdStep 901539 906540) (fun n ↦ signedRowFloor (-1000000000000000) n rows901539)
        5001 ⟨901539, 901720685380952995, 901727049257808867, 1046222929973740, 1046235522765251⟩ =
      true := by
  decide +kernel

private theorem row_901539 {r : SignedPsiRow} (hr : r ∈ rows901539) (ha : 901539 ≤ r.left + 1)
    (hb : r.right < 906540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_901539 (by decide) (by decide) (by decide) rows_901539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_901539 {x : ℝ} (hl : 901539 ≤ x) (hu : x ≤ 906539) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_901539 (r := ⟨901539, 906539, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows906539 : List SignedPsiRow :=
  [⟨906539, 909664, -119000000000000⟩, ⟨910106, 911539, 0⟩]

private theorem rows_906539_checked :
    signedWalk (gcdStep 906539 911540) (fun n ↦ signedRowFloor (-1000000000000000) n rows906539)
        5001 ⟨906539, 906603126071419620, 906609492378114731, 1046222929973740, 1046235522765251⟩ =
      true := by
  decide +kernel

private theorem row_906539 {r : SignedPsiRow} (hr : r ∈ rows906539) (ha : 906539 ≤ r.left + 1)
    (hb : r.right < 911540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_906539 (by decide) (by decide) (by decide) rows_906539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_906539 {x : ℝ} (hl : 906539 ≤ x) (hu : x ≤ 909664) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_906539 (r := ⟨906539, 909664, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_906539 {x : ℝ} (hl : 910106 ≤ x) (hu : x ≤ 911539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_906539 (r := ⟨910106, 911539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows911539 : List SignedPsiRow :=
  [⟨911539, 916539, 0⟩]

private theorem rows_911539_checked :
    signedWalk (gcdStep 911539 916540) (fun n ↦ signedRowFloor (-1000000000000000) n rows911539)
        5001 ⟨911539, 911892214537799288, 911898596014063683, 1053082544590572, 1053095182829703⟩ =
      true := by
  decide +kernel

private theorem row_911539 {r : SignedPsiRow} (hr : r ∈ rows911539) (ha : 911539 ≤ r.left + 1)
    (hb : r.right < 916540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_911539 (by decide) (by decide) (by decide) rows_911539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_911539 {x : ℝ} (hl : 911539 ≤ x) (hu : x ≤ 916539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_911539 (r := ⟨911539, 916539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows916539 : List SignedPsiRow :=
  [⟨916539, 921539, 0⟩]

private theorem rows_916539_checked :
    signedWalk (gcdStep 916539 921540) (fun n ↦ signedRowFloor (-1000000000000000) n rows916539)
        5001 ⟨916539, 916673325082273885, 916679743113070684, 1057657255195228, 1057669947687839⟩ =
      true := by
  decide +kernel

private theorem row_916539 {r : SignedPsiRow} (hr : r ∈ rows916539) (ha : 916539 ≤ r.left + 1)
    (hb : r.right < 921540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_916539 (by decide) (by decide) (by decide) rows_916539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 141 in this batch. -/
public theorem psi_cell141_916539 {x : ℝ} (hl : 916539 ≤ x) (hu : x ≤ 921539) :
    0 ≤ Chebyshev.psi x - x := by
  have h :=
    row_916539 (r := ⟨916539, 921539, 0⟩) (by decide) (by decide) (by decide) (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
