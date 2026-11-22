/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 61539 to 66539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e61539 : Edge :=
  ⟨61539, 61556418269392894, 61556951470195781, 285919808194029, 285922634206487⟩

private def e66539 : Edge :=
  ⟨66539, 66492899855141710, 66493451560970070, 297687483794043, 297690390601889⟩

private def extra61539 : ℕ → ℕ
  | 61539 => 133
  | 61673 => 163
  | 61837 => 165
  | 62003 => 139
  | 62143 => 167
  | 62311 => 189
  | 62501 => 185
  | 62687 => 215
  | 62903 => 188
  | 63092 => 177
  | 63270 => 133
  | 63404 => 176
  | 63581 => 145
  | 63727 => 125
  | 63853 => 159
  | 64013 => 175
  | 64189 => 213
  | 64403 => 199
  | 64603 => 155
  | 64759 => 143
  | 64903 => 144
  | 65048 => 132
  | 65181 => 177
  | 65359 => 155
  | 65515 => 132
  | 65648 => 189
  | 65838 => 202
  | 66041 => 207
  | 66249 => 178
  | 66428 => 110
  | _ => 0

private theorem part61539 : Segment Valid highEstimate e61539 e66539 := by
  apply gcd_batch (by decide) (by decide) extra61539 30
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [61539,66539). -/
theorem batch61539 :
    Segment Valid highEstimate
      ⟨61539, 61556418269392894, 61556951470195781, 285919808194029, 285922634206487⟩
      ⟨66539, 66492899855141710, 66493451560970070, 297687483794043, 297690390601889⟩ := by
  exact part61539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
