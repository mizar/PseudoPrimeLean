/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 556539 to 561539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e556539 : Edge :=
  ⟨556539, 556405675189643609, 556409682461398322, 836512506291081, 836523164081411⟩

private def e561539 : Edge :=
  ⟨561539, 561513965587696661, 561517999202475834, 836512506291081, 836523164081411⟩

private def extra556539 : ℕ → ℕ
  | 556539 => 462
  | 557002 => 608
  | 557611 => 542
  | 558154 => 515
  | 558670 => 516
  | 559187 => 462
  | 559650 => 515
  | 560166 => 556
  | 560723 => 583
  | 561307 => 231
  | _ => 0

private theorem part556539 : Segment Valid highEstimate e556539 e561539 := by
  apply gcd_batch (by decide) (by decide) extra556539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [556539,561539). -/
theorem batch556539 :
    Segment Valid highEstimate
      ⟨556539, 556405675189643609, 556409682461398322, 836512506291081, 836523164081411⟩
      ⟨561539, 561513965587696661, 561517999202475834, 836512506291081, 836523164081411⟩ := by
  exact part556539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
