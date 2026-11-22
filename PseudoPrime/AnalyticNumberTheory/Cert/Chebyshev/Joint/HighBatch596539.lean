/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 596539 to 601539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e596539 : Edge :=
  ⟨596539, 596668087217080912, 596672479552492739, 867461836088443, 867472870489804⟩

private def e601539 : Edge :=
  ⟨601539, 601650083532281086, 601654522595905655, 874112115045486, 874123170639620⟩

private def extra596539 : ℕ → ℕ
  | 596539 => 423
  | 596963 => 455
  | 597419 => 413
  | 597833 => 473
  | 598307 => 491
  | 598799 => 521
  | 599321 => 521
  | 599843 => 515
  | 600359 => 523
  | 600883 => 449
  | 601333 => 205
  | _ => 0

private theorem part596539 : Segment Valid highEstimate e596539 e601539 := by
  apply gcd_batch (by decide) (by decide) extra596539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [596539,601539). -/
theorem batch596539 :
    Segment Valid highEstimate
      ⟨596539, 596668087217080912, 596672479552492739, 867461836088443, 867472870489804⟩
      ⟨601539, 601650083532281086, 601654522595905655, 874112115045486, 874123170639620⟩ := by
  exact part596539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
