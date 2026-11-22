/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 351539 to 356539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e351539 : Edge :=
  ⟨351539, 351754154763738223, 351756956336323203, 655259656683198, 655267971326173⟩

private def e356539 : Edge :=
  ⟨356539, 356781923285159961, 356784746846589057, 661644851080582, 661653167150248⟩

private def extra351539 : ℕ → ℕ
  | 351539 => 263
  | 351803 => 269
  | 352073 => 275
  | 352349 => 199
  | 352549 => 221
  | 352771 => 239
  | 353011 => 225
  | 353237 => 251
  | 353489 => 257
  | 353747 => 253
  | 354001 => 245
  | 354247 => 153
  | 354401 => 151
  | 354553 => 173
  | 354727 => 153
  | 354881 => 145
  | 355027 => 81
  | 355109 => 151
  | 355261 => 179
  | 355441 => 129
  | 355571 => 145
  | 355717 => 129
  | 355847 => 119
  | 355967 => 169
  | 356137 => 189
  | 356327 => 211
  | _ => 0

private theorem part351539 : Segment Valid highEstimate e351539 e356539 := by
  apply gcd_batch (by decide) (by decide) extra351539 26
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [351539,356539). -/
theorem batch351539 :
    Segment Valid highEstimate
      ⟨351539, 351754154763738223, 351756956336323203, 655259656683198, 655267971326173⟩
      ⟨356539, 356781923285159961, 356784746846589057, 661644851080582, 661653167150248⟩ := by
  exact part351539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
