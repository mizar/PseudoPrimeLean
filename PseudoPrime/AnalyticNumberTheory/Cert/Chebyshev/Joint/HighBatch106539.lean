/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 106539 to 111539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e106539 : Edge :=
  ⟨106539, 106549429284512030, 106550353297655247, 375783751498545, 375788393804346⟩

private def e111539 : Edge :=
  ⟨111539, 111484944561403024, 111485890653785676, 381585869620603, 381590553754195⟩

private def extra106539 : ℕ → ℕ
  | 106539 => 213
  | 106753 => 207
  | 106961 => 221
  | 107183 => 269
  | 107453 => 259
  | 107713 => 197
  | 107911 => 208
  | 108120 => 208
  | 108329 => 232
  | 108562 => 243
  | 108806 => 208
  | 109015 => 266
  | 109282 => 254
  | 109537 => 269
  | 109807 => 251
  | 110059 => 282
  | 110342 => 232
  | 110575 => 220
  | 110796 => 209
  | 111006 => 243
  | 111250 => 221
  | 111472 => 66
  | _ => 0

private theorem part106539 : Segment Valid highEstimate e106539 e111539 := by
  apply gcd_batch (by decide) (by decide) extra106539 22
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [106539,111539). -/
theorem batch106539 :
    Segment Valid highEstimate
      ⟨106539, 106549429284512030, 106550353297655247, 375783751498545, 375788393804346⟩
      ⟨111539, 111484944561403024, 111485890653785676, 381585869620603, 381590553754195⟩ := by
  exact part106539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
