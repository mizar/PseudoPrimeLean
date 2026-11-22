/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 146539 to 151539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e146539 : Edge :=
  ⟨146539, 146524007745593682, 146525211438669482, 434208105237132, 434213452403432⟩

private def e151539 : Edge :=
  ⟨151539, 151638276828159825, 151639551791847855, 450090008633458, 450095613867576⟩

private def extra146539 : ℕ → ℕ
  | 146539 => 302
  | 146842 => 276
  | 147119 => 273
  | 147393 => 298
  | 147692 => 309
  | 148002 => 273
  | 148276 => 250
  | 148527 => 250
  | 148778 => 237
  | 149016 => 262
  | 149279 => 251
  | 149531 => 259
  | 149791 => 269
  | 150061 => 239
  | 150301 => 249
  | 150551 => 281
  | 150833 => 223
  | 151057 => 231
  | 151289 => 227
  | 151517 => 21
  | _ => 0

private theorem part146539 : Segment Valid highEstimate e146539 e151539 := by
  apply gcd_batch (by decide) (by decide) extra146539 20
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [146539,151539). -/
theorem batch146539 :
    Segment Valid highEstimate
      ⟨146539, 146524007745593682, 146525211438669482, 434208105237132, 434213452403432⟩
      ⟨151539, 151638276828159825, 151639551791847855, 450090008633458, 450095613867576⟩ := by
  exact part146539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
