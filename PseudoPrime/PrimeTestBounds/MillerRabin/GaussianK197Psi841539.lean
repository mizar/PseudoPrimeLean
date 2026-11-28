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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch841539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch846539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch851539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch856539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch861539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch866539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch871539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch876539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 841539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_841539 :
    Valid ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  have h761539 := (joined721539To761539 h721539).1
  have h801539 := (joined761539To801539 h761539).1
  have h841539 := (joined801539To841539 h801539).1
  exact h841539

private theorem seed_846539 :
    Valid ⟨846539, 846587630139856280, 846593726294926399, 1018845896939750, 1018858338951882⟩ :=
  (batch841539 seed_841539).1

private theorem seed_851539 :
    Valid ⟨851539, 851611514203447833, 851617658626068577, 1018845896939750, 1018858338951882⟩ :=
  (batch846539 seed_846539).1

private theorem seed_856539 :
    Valid ⟨856539, 856500997878603721, 856507149722914125, 1018845896939750, 1018858338951882⟩ :=
  (batch851539 seed_851539).1

private theorem seed_861539 :
    Valid ⟨861539, 861460856494600496, 861467021221729155, 1018845896939750, 1018858338951882⟩ :=
  (batch856539 seed_856539).1

private theorem seed_866539 :
    Valid ⟨866539, 866648357554937652, 866654560527808931, 1025680005678137, 1025692448270876⟩ :=
  (batch861539 seed_861539).1

private theorem seed_871539 :
    Valid ⟨871539, 871708131014049436, 871714357291642464, 1025680005678137, 1025692448270876⟩ :=
  (batch866539 seed_866539).1

private theorem seed_876539 :
    Valid ⟨876539, 876756398738757828, 876762633607524403, 1025680005678137, 1025692448270876⟩ :=
  (batch871539 seed_871539).1

private def rows841539 : List SignedPsiRow :=
  [⟨841539, 846539, -154000000000000⟩]

private theorem rows_841539_checked :
    signedWalk (gcdStep 841539 846540) (fun n ↦ signedRowFloor (-1000000000000000) n rows841539)
        5001 ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩ =
      true := by
  decide +kernel

private theorem row_841539 {r : SignedPsiRow} (hr : r ∈ rows841539) (ha : 841539 ≤ r.left + 1)
    (hb : r.right < 846540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_841539 (by decide) (by decide) (by decide) rows_841539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_841539 {x : ℝ} (hl : 841539 ≤ x) (hu : x ≤ 846539) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_841539 (r := ⟨841539, 846539, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows846539 : List SignedPsiRow :=
  [⟨846539, 847262, -154000000000000⟩, ⟨847704, 851539, -139000000000000⟩]

private theorem rows_846539_checked :
    signedWalk (gcdStep 846539 851540) (fun n ↦ signedRowFloor (-1000000000000000) n rows846539)
        5001 ⟨846539, 846587630139856280, 846593726294926399, 1018845896939750, 1018858338951882⟩ =
      true := by
  decide +kernel

private theorem row_846539 {r : SignedPsiRow} (hr : r ∈ rows846539) (ha : 846539 ≤ r.left + 1)
    (hb : r.right < 851540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_846539 (by decide) (by decide) (by decide) rows_846539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_846539 {x : ℝ} (hl : 846539 ≤ x) (hu : x ≤ 847262) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_846539 (r := ⟨846539, 847262, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_846539 {x : ℝ} (hl : 847704 ≤ x) (hu : x ≤ 851539) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_846539 (r := ⟨847704, 851539, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows851539 : List SignedPsiRow :=
  [⟨851539, 856539, -139000000000000⟩]

private theorem rows_851539_checked :
    signedWalk (gcdStep 851539 856540) (fun n ↦ signedRowFloor (-1000000000000000) n rows851539)
        5001 ⟨851539, 851611514203447833, 851617658626068577, 1018845896939750, 1018858338951882⟩ =
      true := by
  decide +kernel

private theorem row_851539 {r : SignedPsiRow} (hr : r ∈ rows851539) (ha : 851539 ≤ r.left + 1)
    (hb : r.right < 856540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_851539 (by decide) (by decide) (by decide) rows_851539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_851539 {x : ℝ} (hl : 851539 ≤ x) (hu : x ≤ 856539) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_851539 (r := ⟨851539, 856539, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows856539 : List SignedPsiRow :=
  [⟨856539, 861539, -139000000000000⟩]

private theorem rows_856539_checked :
    signedWalk (gcdStep 856539 861540) (fun n ↦ signedRowFloor (-1000000000000000) n rows856539)
        5001 ⟨856539, 856500997878603721, 856507149722914125, 1018845896939750, 1018858338951882⟩ =
      true := by
  decide +kernel

private theorem row_856539 {r : SignedPsiRow} (hr : r ∈ rows856539) (ha : 856539 ≤ r.left + 1)
    (hb : r.right < 861540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_856539 (by decide) (by decide) (by decide) rows_856539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_856539 {x : ℝ} (hl : 856539 ≤ x) (hu : x ≤ 861539) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_856539 (r := ⟨856539, 861539, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows861539 : List SignedPsiRow :=
  [⟨861539, 866539, -139000000000000⟩]

private theorem rows_861539_checked :
    signedWalk (gcdStep 861539 866540) (fun n ↦ signedRowFloor (-1000000000000000) n rows861539)
        5001 ⟨861539, 861460856494600496, 861467021221729155, 1018845896939750, 1018858338951882⟩ =
      true := by
  decide +kernel

private theorem row_861539 {r : SignedPsiRow} (hr : r ∈ rows861539) (ha : 861539 ≤ r.left + 1)
    (hb : r.right < 866540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_861539 (by decide) (by decide) (by decide) rows_861539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_861539 {x : ℝ} (hl : 861539 ≤ x) (hu : x ≤ 866539) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_861539 (r := ⟨861539, 866539, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows866539 : List SignedPsiRow :=
  [⟨866539, 871539, -139000000000000⟩]

private theorem rows_866539_checked :
    signedWalk (gcdStep 866539 871540) (fun n ↦ signedRowFloor (-1000000000000000) n rows866539)
        5001 ⟨866539, 866648357554937652, 866654560527808931, 1025680005678137, 1025692448270876⟩ =
      true := by
  decide +kernel

private theorem row_866539 {r : SignedPsiRow} (hr : r ∈ rows866539) (ha : 866539 ≤ r.left + 1)
    (hb : r.right < 871540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_866539 (by decide) (by decide) (by decide) rows_866539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_866539 {x : ℝ} (hl : 866539 ≤ x) (hu : x ≤ 871539) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_866539 (r := ⟨866539, 871539, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows871539 : List SignedPsiRow :=
  [⟨871539, 876539, -139000000000000⟩]

private theorem rows_871539_checked :
    signedWalk (gcdStep 871539 876540) (fun n ↦ signedRowFloor (-1000000000000000) n rows871539)
        5001 ⟨871539, 871708131014049436, 871714357291642464, 1025680005678137, 1025692448270876⟩ =
      true := by
  decide +kernel

private theorem row_871539 {r : SignedPsiRow} (hr : r ∈ rows871539) (ha : 871539 ≤ r.left + 1)
    (hb : r.right < 876540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_871539 (by decide) (by decide) (by decide) rows_871539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_871539 {x : ℝ} (hl : 871539 ≤ x) (hu : x ≤ 876539) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_871539 (r := ⟨871539, 876539, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows876539 : List SignedPsiRow :=
  [⟨876539, 878186, -139000000000000⟩, ⟨878628, 881539, -119000000000000⟩]

private theorem rows_876539_checked :
    signedWalk (gcdStep 876539 881540) (fun n ↦ signedRowFloor (-1000000000000000) n rows876539)
        5001 ⟨876539, 876756398738757828, 876762633607524403, 1025680005678137, 1025692448270876⟩ =
      true := by
  decide +kernel

private theorem row_876539 {r : SignedPsiRow} (hr : r ∈ rows876539) (ha : 876539 ≤ r.left + 1)
    (hb : r.right < 881540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_876539 (by decide) (by decide) (by decide) rows_876539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 139 in this batch. -/
public theorem psi_cell139_876539 {x : ℝ} (hl : 876539 ≤ x) (hu : x ≤ 878186) :
    -139 ≤ Chebyshev.psi x - x := by
  have h :=
    row_876539 (r := ⟨876539, 878186, -139000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 140 in this batch. -/
public theorem psi_cell140_876539 {x : ℝ} (hl : 878628 ≤ x) (hu : x ≤ 881539) :
    -119 ≤ Chebyshev.psi x - x := by
  have h :=
    row_876539 (r := ⟨878628, 881539, -119000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
