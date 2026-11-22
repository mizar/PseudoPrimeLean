/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 976539 to 981539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e976539 : Edge :=
  ⟨976539, 976603172512363965, 976609795810791725, 1088618862387204, 1088631673355392⟩

private def e981539 : Edge :=
  ⟨981539, 981348438476331104, 981355090621901309, 1088618862387204, 1088631673355392⟩

private def extra976539 : ℕ → ℕ
  | 976539 => 823
  | 977363 => 761
  | 978125 => 703
  | 978829 => 716
  | 979546 => 758
  | 980305 => 565
  | 980871 => 523
  | 981395 => 143
  | _ => 0

private theorem part976539 : Segment Valid highEstimate e976539 e981539 := by
  apply gcd_batch (by decide) (by decide) extra976539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [976539,981539). -/
theorem batch976539 :
    Segment Valid highEstimate
      ⟨976539, 976603172512363965, 976609795810791725, 1088618862387204, 1088631673355392⟩
      ⟨981539, 981348438476331104, 981355090621901309, 1088618862387204, 1088631673355392⟩ := by
  exact part976539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
