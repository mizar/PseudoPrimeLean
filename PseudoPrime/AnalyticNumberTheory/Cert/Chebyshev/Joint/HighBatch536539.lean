/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 536539 to 541539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e536539 : Edge :=
  ⟨536539, 536701085652854120, 536704810452442472, 816699368866669, 816709810119861⟩

private def e541539 : Edge :=
  ⟨541539, 541577557633886101, 541581396707376733, 823296512632682, 823307116887428⟩

private def extra536539 : ℕ → ℕ
  | 536539 => 383
  | 536923 => 317
  | 537241 => 437
  | 537679 => 467
  | 538147 => 431
  | 538579 => 459
  | 539039 => 439
  | 539479 => 513
  | 539993 => 523
  | 540517 => 543
  | 541061 => 477
  | _ => 0

private theorem part536539 : Segment Valid highEstimate e536539 e541539 := by
  apply gcd_batch (by decide) (by decide) extra536539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [536539,541539). -/
theorem batch536539 :
    Segment Valid highEstimate
      ⟨536539, 536701085652854120, 536704810452442472, 816699368866669, 816709810119861⟩
      ⟨541539, 541577557633886101, 541581396707376733, 823296512632682, 823307116887428⟩ := by
  exact part536539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
