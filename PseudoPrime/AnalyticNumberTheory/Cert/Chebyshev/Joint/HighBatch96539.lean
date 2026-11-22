/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 96539 to 101539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e96539 : Edge :=
  ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩

private def e101539 : Edge :=
  ⟨101539, 101601127196570818, 101602017656699515, 371933603896840, 371938246202635⟩

private def extra96539 : ℕ → ℕ
  | 96539 => 181
  | 96721 => 129
  | 96851 => 145
  | 96997 => 161
  | 97159 => 209
  | 97369 => 183
  | 97553 => 223
  | 97777 => 191
  | 97969 => 251
  | 98221 => 237
  | 98459 => 253
  | 98713 => 215
  | 98929 => 201
  | 99131 => 215
  | 99347 => 215
  | 99563 => 203
  | 99767 => 203
  | 99971 => 221
  | 100193 => 223
  | 100417 => 231
  | 100649 => 273
  | 100923 => 219
  | 101143 => 233
  | 101377 => 161
  | _ => 0

private theorem part96539 : Segment Valid highEstimate e96539 e101539 := by
  apply gcd_batch (by decide) (by decide) extra96539 24
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [96539,101539). -/
theorem batch96539 :
    Segment Valid highEstimate
      ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩
      ⟨101539, 101601127196570818, 101602017656699515, 371933603896840, 371938246202635⟩ := by
  exact part96539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
