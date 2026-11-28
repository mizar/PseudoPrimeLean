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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch721539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch726539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch731539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch736539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch741539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch746539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch751539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch756539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 721539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_721539 :
    Valid ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  exact h721539

private theorem seed_726539 :
    Valid ⟨726539, 726568256142213967, 726573694285358171, 942304906054199, 942316637549039⟩ :=
  (batch721539 seed_721539).1

private theorem seed_731539 :
    Valid ⟨731539, 731529303067427572, 731534765250192739, 949053665533654, 949065414411248⟩ :=
  (batch726539 seed_726539).1

private theorem seed_736539 :
    Valid ⟨736539, 736654950214771859, 736660476226230268, 955807103056896, 955818908254589⟩ :=
  (batch731539 seed_731539).1

private theorem seed_741539 :
    Valid ⟨741539, 741593991365195835, 741599531318049378, 962562871258316, 962574760588496⟩ :=
  (batch736539 seed_736539).1

private theorem seed_746539 :
    Valid ⟨746539, 746305661307613763, 746311216772775337, 969323284128657, 969335329903535⟩ :=
  (batch741539 seed_741539).1

private theorem seed_751539 :
    Valid ⟨751539, 751242872242326510, 751248475187821155, 969323284128657, 969335329903535⟩ :=
  (batch746539 seed_746539).1

private theorem seed_756539 :
    Valid ⟨756539, 756263657967447517, 756269295156134704, 969323284128657, 969335329903535⟩ :=
  (batch751539 seed_751539).1

private def rows721539 : List SignedPsiRow :=
  [⟨721539, 726539, -271000000000000⟩]

private theorem rows_721539_checked :
    signedWalk (gcdStep 721539 726540) (fun n ↦ signedRowFloor (-1000000000000000) n rows721539)
        5001 ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩ =
      true := by
  decide +kernel

private theorem row_721539 {r : SignedPsiRow} (hr : r ∈ rows721539) (ha : 721539 ≤ r.left + 1)
    (hb : r.right < 726540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_721539 (by decide) (by decide) (by decide) rows_721539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_721539 {x : ℝ} (hl : 721539 ≤ x) (hu : x ≤ 726539) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_721539 (r := ⟨721539, 726539, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows726539 : List SignedPsiRow :=
  [⟨726539, 729110, -271000000000000⟩, ⟨729550, 731539, -412000000000000⟩]

private theorem rows_726539_checked :
    signedWalk (gcdStep 726539 731540) (fun n ↦ signedRowFloor (-1000000000000000) n rows726539)
        5001 ⟨726539, 726568256142213967, 726573694285358171, 942304906054199, 942316637549039⟩ =
      true := by
  decide +kernel

private theorem row_726539 {r : SignedPsiRow} (hr : r ∈ rows726539) (ha : 726539 ≤ r.left + 1)
    (hb : r.right < 731540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_726539 (by decide) (by decide) (by decide) rows_726539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 134 in this batch. -/
public theorem psi_cell134_726539 {x : ℝ} (hl : 726539 ≤ x) (hu : x ≤ 729110) :
    -271 ≤ Chebyshev.psi x - x := by
  have h :=
    row_726539 (r := ⟨726539, 729110, -271000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_726539 {x : ℝ} (hl : 729550 ≤ x) (hu : x ≤ 731539) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_726539 (r := ⟨729550, 731539, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows731539 : List SignedPsiRow :=
  [⟨731539, 736539, -412000000000000⟩]

private theorem rows_731539_checked :
    signedWalk (gcdStep 731539 736540) (fun n ↦ signedRowFloor (-1000000000000000) n rows731539)
        5001 ⟨731539, 731529303067427572, 731534765250192739, 949053665533654, 949065414411248⟩ =
      true := by
  decide +kernel

private theorem row_731539 {r : SignedPsiRow} (hr : r ∈ rows731539) (ha : 731539 ≤ r.left + 1)
    (hb : r.right < 736540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_731539 (by decide) (by decide) (by decide) rows_731539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_731539 {x : ℝ} (hl : 731539 ≤ x) (hu : x ≤ 736539) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_731539 (r := ⟨731539, 736539, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows736539 : List SignedPsiRow :=
  [⟨736539, 741539, -412000000000000⟩]

private theorem rows_736539_checked :
    signedWalk (gcdStep 736539 741540) (fun n ↦ signedRowFloor (-1000000000000000) n rows736539)
        5001 ⟨736539, 736654950214771859, 736660476226230268, 955807103056896, 955818908254589⟩ =
      true := by
  decide +kernel

private theorem row_736539 {r : SignedPsiRow} (hr : r ∈ rows736539) (ha : 736539 ≤ r.left + 1)
    (hb : r.right < 741540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_736539 (by decide) (by decide) (by decide) rows_736539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_736539 {x : ℝ} (hl : 736539 ≤ x) (hu : x ≤ 741539) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_736539 (r := ⟨736539, 741539, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows741539 : List SignedPsiRow :=
  [⟨741539, 746539, -412000000000000⟩]

private theorem rows_741539_checked :
    signedWalk (gcdStep 741539 746540) (fun n ↦ signedRowFloor (-1000000000000000) n rows741539)
        5001 ⟨741539, 741593991365195835, 741599531318049378, 962562871258316, 962574760588496⟩ =
      true := by
  decide +kernel

private theorem row_741539 {r : SignedPsiRow} (hr : r ∈ rows741539) (ha : 741539 ≤ r.left + 1)
    (hb : r.right < 746540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_741539 (by decide) (by decide) (by decide) rows_741539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_741539 {x : ℝ} (hl : 741539 ≤ x) (hu : x ≤ 746539) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_741539 (r := ⟨741539, 746539, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows746539 : List SignedPsiRow :=
  [⟨746539, 751539, -412000000000000⟩]

private theorem rows_746539_checked :
    signedWalk (gcdStep 746539 751540) (fun n ↦ signedRowFloor (-1000000000000000) n rows746539)
        5001 ⟨746539, 746305661307613763, 746311216772775337, 969323284128657, 969335329903535⟩ =
      true := by
  decide +kernel

private theorem row_746539 {r : SignedPsiRow} (hr : r ∈ rows746539) (ha : 746539 ≤ r.left + 1)
    (hb : r.right < 751540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_746539 (by decide) (by decide) (by decide) rows_746539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_746539 {x : ℝ} (hl : 746539 ≤ x) (hu : x ≤ 751539) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_746539 (r := ⟨746539, 751539, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows751539 : List SignedPsiRow :=
  [⟨751539, 756539, -412000000000000⟩]

private theorem rows_751539_checked :
    signedWalk (gcdStep 751539 756540) (fun n ↦ signedRowFloor (-1000000000000000) n rows751539)
        5001 ⟨751539, 751242872242326510, 751248475187821155, 969323284128657, 969335329903535⟩ =
      true := by
  decide +kernel

private theorem row_751539 {r : SignedPsiRow} (hr : r ∈ rows751539) (ha : 751539 ≤ r.left + 1)
    (hb : r.right < 756540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_751539 (by decide) (by decide) (by decide) rows_751539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_751539 {x : ℝ} (hl : 751539 ≤ x) (hu : x ≤ 756539) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_751539 (r := ⟨751539, 756539, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows756539 : List SignedPsiRow :=
  [⟨756539, 757816, -412000000000000⟩, ⟨758257, 761539, -396000000000000⟩]

private theorem rows_756539_checked :
    signedWalk (gcdStep 756539 761540) (fun n ↦ signedRowFloor (-1000000000000000) n rows756539)
        5001 ⟨756539, 756263657967447517, 756269295156134704, 969323284128657, 969335329903535⟩ =
      true := by
  decide +kernel

private theorem row_756539 {r : SignedPsiRow} (hr : r ∈ rows756539) (ha : 756539 ≤ r.left + 1)
    (hb : r.right < 761540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_756539 (by decide) (by decide) (by decide) rows_756539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 135 in this batch. -/
public theorem psi_cell135_756539 {x : ℝ} (hl : 756539 ≤ x) (hu : x ≤ 757816) :
    -412 ≤ Chebyshev.psi x - x := by
  have h :=
    row_756539 (r := ⟨756539, 757816, -412000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 136 in this batch. -/
public theorem psi_cell136_756539 {x : ℝ} (hl : 758257 ≤ x) (hu : x ≤ 761539) :
    -396 ≤ Chebyshev.psi x - x := by
  have h :=
    row_756539 (r := ⟨758257, 761539, -396000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
