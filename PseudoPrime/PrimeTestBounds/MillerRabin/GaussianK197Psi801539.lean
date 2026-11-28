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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch801539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch806539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch811539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch816539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch821539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch826539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch831539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch836539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 801539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_801539 :
    Valid ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  have h681539 := (joined641539To681539 h641539).1
  have h721539 := (joined681539To721539 h681539).1
  have h761539 := (joined721539To761539 h721539).1
  have h801539 := (joined761539To801539 h761539).1
  exact h801539

private theorem seed_806539 :
    Valid ⟨806539, 806712479534722463, 806718393580556253, 996452017626611, 996464214691058⟩ :=
  (batch801539 seed_801539).1

private theorem seed_811539 :
    Valid ⟨811539, 811596205015537406, 811602130658988895, 996452017626611, 996464214691058⟩ :=
  (batch806539 seed_806539).1

private theorem seed_816539 :
    Valid ⟨816539, 816495703074948022, 816501664248279778, 996452017626611, 996464214691058⟩ :=
  (batch811539 seed_811539).1

private theorem seed_821539 :
    Valid ⟨821539, 821588046766904406, 821594041367152941, 996452017626611, 996464214691058⟩ :=
  (batch816539 seed_816539).1

private theorem seed_826539 :
    Valid ⟨826539, 826800389560951416, 826806391435947923, 1005208069614610, 1005220342038805⟩ :=
  (batch821539 seed_821539).1

private theorem seed_831539 :
    Valid ⟨831539, 831686021554378298, 831692049791385777, 1012022610967268, 1012035023523210⟩ :=
  (batch826539 seed_826539).1

private theorem seed_836539 :
    Valid ⟨836539, 836744205537533115, 836750279065628673, 1012022610967268, 1012035023523210⟩ :=
  (batch831539 seed_831539).1

private def rows801539 : List SignedPsiRow :=
  [⟨801539, 806539, -103000000000000⟩]

private theorem rows_801539_checked :
    signedWalk (gcdStep 801539 806540) (fun n ↦ signedRowFloor (-1000000000000000) n rows801539)
        5001 ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_801539 {r : SignedPsiRow} (hr : r ∈ rows801539) (ha : 801539 ≤ r.left + 1)
    (hb : r.right < 806540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_801539 (by decide) (by decide) (by decide) rows_801539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_801539 {x : ℝ} (hl : 801539 ≤ x) (hu : x ≤ 806539) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_801539 (r := ⟨801539, 806539, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows806539 : List SignedPsiRow :=
  [⟨806539, 811539, -103000000000000⟩]

private theorem rows_806539_checked :
    signedWalk (gcdStep 806539 811540) (fun n ↦ signedRowFloor (-1000000000000000) n rows806539)
        5001 ⟨806539, 806712479534722463, 806718393580556253, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_806539 {r : SignedPsiRow} (hr : r ∈ rows806539) (ha : 806539 ≤ r.left + 1)
    (hb : r.right < 811540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_806539 (by decide) (by decide) (by decide) rows_806539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_806539 {x : ℝ} (hl : 806539 ≤ x) (hu : x ≤ 811539) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_806539 (r := ⟨806539, 811539, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows811539 : List SignedPsiRow :=
  [⟨811539, 816539, -103000000000000⟩]

private theorem rows_811539_checked :
    signedWalk (gcdStep 811539 816540) (fun n ↦ signedRowFloor (-1000000000000000) n rows811539)
        5001 ⟨811539, 811596205015537406, 811602130658988895, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_811539 {r : SignedPsiRow} (hr : r ∈ rows811539) (ha : 811539 ≤ r.left + 1)
    (hb : r.right < 816540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_811539 (by decide) (by decide) (by decide) rows_811539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_811539 {x : ℝ} (hl : 811539 ≤ x) (hu : x ≤ 816539) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_811539 (r := ⟨811539, 816539, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows816539 : List SignedPsiRow :=
  [⟨816539, 816893, -103000000000000⟩, ⟨817334, 821539, -154000000000000⟩]

private theorem rows_816539_checked :
    signedWalk (gcdStep 816539 821540) (fun n ↦ signedRowFloor (-1000000000000000) n rows816539)
        5001 ⟨816539, 816495703074948022, 816501664248279778, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_816539 {r : SignedPsiRow} (hr : r ∈ rows816539) (ha : 816539 ≤ r.left + 1)
    (hb : r.right < 821540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_816539 (by decide) (by decide) (by decide) rows_816539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 137 in this batch. -/
public theorem psi_cell137_816539 {x : ℝ} (hl : 816539 ≤ x) (hu : x ≤ 816893) :
    -103 ≤ Chebyshev.psi x - x := by
  have h :=
    row_816539 (r := ⟨816539, 816893, -103000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_816539 {x : ℝ} (hl : 817334 ≤ x) (hu : x ≤ 821539) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_816539 (r := ⟨817334, 821539, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows821539 : List SignedPsiRow :=
  [⟨821539, 826539, -154000000000000⟩]

private theorem rows_821539_checked :
    signedWalk (gcdStep 821539 826540) (fun n ↦ signedRowFloor (-1000000000000000) n rows821539)
        5001 ⟨821539, 821588046766904406, 821594041367152941, 996452017626611, 996464214691058⟩ =
      true := by
  decide +kernel

private theorem row_821539 {r : SignedPsiRow} (hr : r ∈ rows821539) (ha : 821539 ≤ r.left + 1)
    (hb : r.right < 826540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_821539 (by decide) (by decide) (by decide) rows_821539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_821539 {x : ℝ} (hl : 821539 ≤ x) (hu : x ≤ 826539) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_821539 (r := ⟨821539, 826539, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows826539 : List SignedPsiRow :=
  [⟨826539, 831539, -154000000000000⟩]

private theorem rows_826539_checked :
    signedWalk (gcdStep 826539 831540) (fun n ↦ signedRowFloor (-1000000000000000) n rows826539)
        5001 ⟨826539, 826800389560951416, 826806391435947923, 1005208069614610, 1005220342038805⟩ =
      true := by
  decide +kernel

private theorem row_826539 {r : SignedPsiRow} (hr : r ∈ rows826539) (ha : 826539 ≤ r.left + 1)
    (hb : r.right < 831540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_826539 (by decide) (by decide) (by decide) rows_826539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_826539 {x : ℝ} (hl : 826539 ≤ x) (hu : x ≤ 831539) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_826539 (r := ⟨826539, 831539, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows831539 : List SignedPsiRow :=
  [⟨831539, 836539, -154000000000000⟩]

private theorem rows_831539_checked :
    signedWalk (gcdStep 831539 836540) (fun n ↦ signedRowFloor (-1000000000000000) n rows831539)
        5001 ⟨831539, 831686021554378298, 831692049791385777, 1012022610967268, 1012035023523210⟩ =
      true := by
  decide +kernel

private theorem row_831539 {r : SignedPsiRow} (hr : r ∈ rows831539) (ha : 831539 ≤ r.left + 1)
    (hb : r.right < 836540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_831539 (by decide) (by decide) (by decide) rows_831539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_831539 {x : ℝ} (hl : 831539 ≤ x) (hu : x ≤ 836539) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_831539 (r := ⟨831539, 836539, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows836539 : List SignedPsiRow :=
  [⟨836539, 841539, -154000000000000⟩]

private theorem rows_836539_checked :
    signedWalk (gcdStep 836539 841540) (fun n ↦ signedRowFloor (-1000000000000000) n rows836539)
        5001 ⟨836539, 836744205537533115, 836750279065628673, 1012022610967268, 1012035023523210⟩ =
      true := by
  decide +kernel

private theorem row_836539 {r : SignedPsiRow} (hr : r ∈ rows836539) (ha : 836539 ≤ r.left + 1)
    (hb : r.right < 841540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_836539 (by decide) (by decide) (by decide) rows_836539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 138 in this batch. -/
public theorem psi_cell138_836539 {x : ℝ} (hl : 836539 ≤ x) (hu : x ≤ 841539) :
    -154 ≤ Chebyshev.psi x - x := by
  have h :=
    row_836539 (r := ⟨836539, 841539, -154000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
