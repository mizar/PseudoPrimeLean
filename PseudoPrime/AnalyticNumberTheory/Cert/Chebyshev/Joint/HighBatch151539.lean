/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 151539 to 156539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e151539 : Edge :=
  ⟨151539, 151638276828159825, 151639551791847855, 450090008633458, 450095613867576⟩

private def e156539 : Edge :=
  ⟨156539, 156595255550532633, 156596572739483630, 450090008633458, 450095613867576⟩

private def extra151539 : ℕ → ℕ
  | 151539 => 153
  | 151693 => 153
  | 151847 => 169
  | 152017 => 171
  | 152189 => 191
  | 152381 => 157
  | 152539 => 177
  | 152717 => 133
  | 152851 => 129
  | 152981 => 131
  | 153113 => 173
  | 153287 => 161
  | 153449 => 139
  | 153589 => 159
  | 153749 => 199
  | 153949 => 177
  | 154127 => 175
  | 154303 => 189
  | 154493 => 197
  | 154691 => 181
  | 154873 => 207
  | 155081 => 209
  | 155291 => 209
  | 155501 => 169
  | 155671 => 125
  | 155797 => 95
  | 155893 => 177
  | 156071 => 187
  | 156259 => 251
  | 156511 => 27
  | _ => 0

private theorem part151539 : Segment Valid highEstimate e151539 e156539 := by
  apply gcd_batch (by decide) (by decide) extra151539 30
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [151539,156539). -/
theorem batch151539 :
    Segment Valid highEstimate
      ⟨151539, 151638276828159825, 151639551791847855, 450090008633458, 450095613867576⟩
      ⟨156539, 156595255550532633, 156596572739483630, 450090008633458, 450095613867576⟩ := by
  exact part151539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
