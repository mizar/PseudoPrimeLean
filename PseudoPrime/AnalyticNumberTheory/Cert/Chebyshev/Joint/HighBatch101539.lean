/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 101539 to 106539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e101539 : Edge :=
  ⟨101539, 101601127196570818, 101602017656699515, 371933603896840, 371938246202635⟩

private def e106539 : Edge :=
  ⟨106539, 106549429284512030, 106550353297655247, 375783751498545, 375788393804346⟩

private def extra101539 : ℕ → ℕ
  | 101539 => 201
  | 101741 => 197
  | 101939 => 161
  | 102101 => 131
  | 102233 => 125
  | 102359 => 139
  | 102499 => 111
  | 102611 => 151
  | 102763 => 165
  | 102929 => 169
  | 103099 => 257
  | 103357 => 255
  | 103613 => 259
  | 103873 => 219
  | 104093 => 233
  | 104327 => 265
  | 104593 => 209
  | 104803 => 219
  | 105023 => 253
  | 105277 => 239
  | 105517 => 243
  | 105761 => 269
  | 106031 => 253
  | 106285 => 231
  | 106517 => 21
  | _ => 0

private theorem part101539 : Segment Valid highEstimate e101539 e106539 := by
  apply gcd_batch (by decide) (by decide) extra101539 25
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [101539,106539). -/
theorem batch101539 :
    Segment Valid highEstimate
      ⟨101539, 101601127196570818, 101602017656699515, 371933603896840, 371938246202635⟩
      ⟨106539, 106549429284512030, 106550353297655247, 375783751498545, 375788393804346⟩ := by
  exact part101539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
