/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 811539 to 816539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e811539 : Edge :=
  ⟨811539, 811596205015537406, 811602130658988895, 996452017626611, 996464214691058⟩

private def e816539 : Edge :=
  ⟨816539, 816495703074948022, 816501664248279778, 996452017626611, 996464214691058⟩

private def extra811539 : ℕ → ℕ
  | 811539 => 651
  | 812191 => 615
  | 812807 => 635
  | 813443 => 653
  | 814097 => 685
  | 814783 => 707
  | 815491 => 699
  | 816191 => 347
  | _ => 0

private theorem part811539 : Segment Valid highEstimate e811539 e816539 := by
  apply gcd_batch (by decide) (by decide) extra811539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [811539,816539). -/
theorem batch811539 :
    Segment Valid highEstimate
      ⟨811539, 811596205015537406, 811602130658988895, 996452017626611, 996464214691058⟩
      ⟨816539, 816495703074948022, 816501664248279778, 996452017626611, 996464214691058⟩ := by
  exact part811539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
