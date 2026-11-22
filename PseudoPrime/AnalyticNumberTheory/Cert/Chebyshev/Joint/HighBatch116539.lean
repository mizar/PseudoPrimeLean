/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 116539 to 121539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e116539 : Edge :=
  ⟨116539, 116486170396305392, 116487141911824128, 387405952542179, 387410641104636⟩

private def e121539 : Edge :=
  ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩

private def extra116539 : ℕ → ℕ
  | 116539 => 231
  | 116771 => 162
  | 116934 => 186
  | 117121 => 186
  | 117308 => 186
  | 117495 => 151
  | 117647 => 163
  | 117811 => 223
  | 118035 => 221
  | 118257 => 221
  | 118479 => 210
  | 118690 => 186
  | 118877 => 174
  | 119052 => 163
  | 119216 => 174
  | 119391 => 163
  | 119555 => 116
  | 119672 => 140
  | 119813 => 174
  | 119988 => 187
  | 120176 => 186
  | 120363 => 163
  | 120527 => 134
  | 120662 => 151
  | 120814 => 163
  | 120978 => 233
  | 121212 => 222
  | 121435 => 103
  | _ => 0

private theorem part116539 : Segment Valid highEstimate e116539 e121539 := by
  apply gcd_batch (by decide) (by decide) extra116539 28
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [116539,121539). -/
theorem batch116539 :
    Segment Valid highEstimate
      ⟨116539, 116486170396305392, 116487141911824128, 387405952542179, 387410641104636⟩
      ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩ := by
  exact part116539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
