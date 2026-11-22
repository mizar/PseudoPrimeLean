/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 206539 to 211539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e206539 : Edge :=
  ⟨206539, 206527250279922435, 206528931783278320, 518158103756435, 518164190674656⟩

private def e211539 : Edge :=
  ⟨211539, 211690773014747110, 211692481446359927, 524282787143811, 524288876466628⟩

private def extra206539 : ℕ → ℕ
  | 206539 => 351
  | 206891 => 268
  | 207160 => 269
  | 207430 => 280
  | 207711 => 361
  | 208073 => 335
  | 208409 => 311
  | 208721 => 349
  | 209071 => 299
  | 209371 => 287
  | 209659 => 269
  | 209929 => 239
  | 210169 => 189
  | 210359 => 173
  | 210533 => 227
  | 210761 => 199
  | 210961 => 231
  | 211193 => 179
  | 211373 => 165
  | _ => 0

private theorem part206539 : Segment Valid highEstimate e206539 e211539 := by
  apply gcd_batch (by decide) (by decide) extra206539 19
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [206539,211539). -/
theorem batch206539 :
    Segment Valid highEstimate
      ⟨206539, 206527250279922435, 206528931783278320, 518158103756435, 518164190674656⟩
      ⟨211539, 211690773014747110, 211692481446359927, 524282787143811, 524288876466628⟩ := by
  exact part206539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
