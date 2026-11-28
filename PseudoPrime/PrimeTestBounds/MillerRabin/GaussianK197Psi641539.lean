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
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch641539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch646539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch651539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch656539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch661539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch666539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch671539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch676539
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.GcdStep

/-! # Signed K197 boundary estimates near 641539 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem seed_641539 :
    Valid ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩ := by
  have h641539 := (joined321539To641539 (joined3500To321539 prefix3500.1).1).1
  exact h641539

private theorem seed_646539 :
    Valid ⟨646539, 646310721377617524, 646315561248544874, 887461196452993, 887472396843589⟩ :=
  (batch641539 seed_641539).1

private theorem seed_651539 :
    Valid ⟨651539, 651316027203783601, 651320913964596621, 887461196452993, 887472396843589⟩ :=
  (batch646539 seed_646539).1

private theorem seed_656539 :
    Valid ⟨656539, 656330909011565733, 656335872066887132, 894156994899402, 894168258571258⟩ :=
  (batch651539 seed_651539).1

private theorem seed_661539 :
    Valid ⟨661539, 661402273677101359, 661407243801120149, 900855262095811, 900866620298927⟩ :=
  (batch656539 seed_656539).1

private theorem seed_666539 :
    Valid ⟨666539, 666416161902772199, 666421165805543381, 900855262095811, 900866620298927⟩ :=
  (batch661539 seed_661539).1

private theorem seed_671539 :
    Valid ⟨671539, 671325556054094871, 671330641003367806, 900855262095811, 900866620298927⟩ :=
  (batch666539 seed_666539).1

private theorem seed_676539 :
    Valid ⟨676539, 676351726654129048, 676356818643495776, 907565785128918, 907577162104873⟩ :=
  (batch671539 seed_671539).1

private def rows671539 : List SignedPsiRow :=
  [⟨673799, 676539, -379000000000000⟩]

private theorem rows_671539_checked :
    signedWalk (gcdStep 671539 676540) (fun n ↦ signedRowFloor (-1000000000000000) n rows671539)
        5001 ⟨671539, 671325556054094871, 671330641003367806, 900855262095811, 900866620298927⟩ =
      true := by
  decide +kernel

private theorem row_671539 {r : SignedPsiRow} (hr : r ∈ rows671539) (ha : 671539 ≤ r.left + 1)
    (hb : r.right < 676540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_671539 (by decide) (by decide) (by decide) rows_671539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 133 in this batch. -/
public theorem psi_cell133_671539 {x : ℝ} (hl : 673799 ≤ x) (hu : x ≤ 676539) :
    -379 ≤ Chebyshev.psi x - x := by
  have h :=
    row_671539 (r := ⟨673799, 676539, -379000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

private def rows676539 : List SignedPsiRow :=
  [⟨676539, 681539, -379000000000000⟩]

private theorem rows_676539_checked :
    signedWalk (gcdStep 676539 681540) (fun n ↦ signedRowFloor (-1000000000000000) n rows676539)
        5001 ⟨676539, 676351726654129048, 676356818643495776, 907565785128918, 907577162104873⟩ =
      true := by
  decide +kernel

private theorem row_676539 {r : SignedPsiRow} (hr : r ∈ rows676539) (ha : 676539 ≤ r.left + 1)
    (hb : r.right < 681540) (hlt : r.left < r.right) {x : ℝ} (hl : (r.left : ℝ) ≤ x)
    (hu : x ≤ r.right) : (r.floor : ℝ) / scale ≤ Chebyshev.psi x - x :=
  signed_row_of_walk hr seed_676539 (by decide) (by decide) (by decide) rows_676539_checked ha hb
    hlt hl hu

/-- The signed lower bound for the part of compressed cell 133 in this batch. -/
public theorem psi_cell133_676539 {x : ℝ} (hl : 676539 ≤ x) (hu : x ≤ 681539) :
    -379 ≤ Chebyshev.psi x - x := by
  have h :=
    row_676539 (r := ⟨676539, 681539, -379000000000000⟩) (by decide) (by decide) (by decide)
      (by decide) hl hu
  norm_num only [scale, Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_div] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
