/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 201539 to 206539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e201539 : Edge :=
  ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩

private def e206539 : Edge :=
  ⟨206539, 206527250279922435, 206528931783278320, 518158103756435, 518164190674656⟩

private def extra201539 : ℕ → ℕ
  | 201539 => 287
  | 201827 => 301
  | 202129 => 363
  | 202493 => 353
  | 202847 => 330
  | 203178 => 280
  | 203459 => 366
  | 203826 => 293
  | 204120 => 292
  | 204413 => 269
  | 204683 => 280
  | 204964 => 244
  | 205209 => 256
  | 205466 => 284
  | 205751 => 281
  | 206033 => 281
  | 206315 => 223
  | _ => 0

private theorem part201539 : Segment Valid highEstimate e201539 e206539 := by
  apply gcd_batch (by decide) (by decide) extra201539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [201539,206539). -/
theorem batch201539 :
    Segment Valid highEstimate
      ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩
      ⟨206539, 206527250279922435, 206528931783278320, 518158103756435, 518164190674656⟩ := by
  exact part201539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
