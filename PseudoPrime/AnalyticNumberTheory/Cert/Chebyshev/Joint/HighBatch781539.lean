/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 781539 to 786539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e781539 : Edge :=
  ⟨781539, 781532914755499894, 781538680576363060, 989664172811091, 989676338238130⟩

private def e786539 : Edge :=
  ⟨786539, 786473191412509356, 786479016874675260, 989664172811091, 989676338238130⟩

private def extra781539 : ℕ → ℕ
  | 781539 => 651
  | 782191 => 767
  | 782959 => 610
  | 783570 => 624
  | 784195 => 637
  | 784833 => 669
  | 785503 => 693
  | 786197 => 341
  | _ => 0

private theorem part781539 : Segment Valid highEstimate e781539 e786539 := by
  apply gcd_batch (by decide) (by decide) extra781539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [781539,786539). -/
theorem batch781539 :
    Segment Valid highEstimate
      ⟨781539, 781532914755499894, 781538680576363060, 989664172811091, 989676338238130⟩
      ⟨786539, 786473191412509356, 786479016874675260, 989664172811091, 989676338238130⟩ := by
  exact part781539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
