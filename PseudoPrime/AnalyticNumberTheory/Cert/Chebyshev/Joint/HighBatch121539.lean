/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 121539 to 126539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e121539 : Edge :=
  ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩

private def e126539 : Edge :=
  ⟨126539, 126551028502105041, 126552040056599293, 406922726210478, 406927562467084⟩

private def extra121539 : ℕ → ℕ
  | 121539 => 258
  | 121798 => 257
  | 122056 => 270
  | 122327 => 269
  | 122597 => 271
  | 122869 => 294
  | 123164 => 257
  | 123422 => 246
  | 123669 => 271
  | 123941 => 289
  | 124231 => 261
  | 124493 => 275
  | 124769 => 287
  | 125057 => 269
  | 125327 => 282
  | 125610 => 246
  | 125857 => 249
  | 126107 => 251
  | 126359 => 179
  | _ => 0

private theorem part121539 : Segment Valid highEstimate e121539 e126539 := by
  apply gcd_batch (by decide) (by decide) extra121539 19
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [121539,126539). -/
theorem batch121539 :
    Segment Valid highEstimate
      ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩
      ⟨126539, 126551028502105041, 126552040056599293, 406922726210478, 406927562467084⟩ := by
  exact part121539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
