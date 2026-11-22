/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 816539 to 821539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e816539 : Edge :=
  ⟨816539, 816495703074948022, 816501664248279778, 996452017626611, 996464214691058⟩

private def e821539 : Edge :=
  ⟨821539, 821588046766904406, 821594041367152941, 996452017626611, 996464214691058⟩

private def extra816539 : ℕ → ℕ
  | 816539 => 643
  | 817183 => 705
  | 817889 => 745
  | 818635 => 694
  | 819330 => 639
  | 819970 => 678
  | 820649 => 661
  | 821311 => 227
  | _ => 0

private theorem part816539 : Segment Valid highEstimate e816539 e821539 := by
  apply gcd_batch (by decide) (by decide) extra816539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [816539,821539). -/
theorem batch816539 :
    Segment Valid highEstimate
      ⟨816539, 816495703074948022, 816501664248279778, 996452017626611, 996464214691058⟩
      ⟨821539, 821588046766904406, 821594041367152941, 996452017626611, 996464214691058⟩ := by
  exact part816539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
