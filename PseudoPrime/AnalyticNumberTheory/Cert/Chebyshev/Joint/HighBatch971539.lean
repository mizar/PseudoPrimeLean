/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 971539 to 976539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e971539 : Edge :=
  ⟨971539, 971597689847870591, 971604302142994180, 1088618862387204, 1088631673355392⟩

private def e976539 : Edge :=
  ⟨976539, 976603172512363965, 976609795810791725, 1088618862387204, 1088631673355392⟩

private def extra971539 : ℕ → ℕ
  | 971539 => 687
  | 972227 => 713
  | 972941 => 785
  | 973727 => 779
  | 974507 => 685
  | 975193 => 705
  | 975899 => 639
  | _ => 0

private theorem part971539 : Segment Valid highEstimate e971539 e976539 := by
  apply gcd_batch (by decide) (by decide) extra971539 7
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [971539,976539). -/
theorem batch971539 :
    Segment Valid highEstimate
      ⟨971539, 971597689847870591, 971604302142994180, 1088618862387204, 1088631673355392⟩
      ⟨976539, 976603172512363965, 976609795810791725, 1088618862387204, 1088631673355392⟩ := by
  exact part971539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
