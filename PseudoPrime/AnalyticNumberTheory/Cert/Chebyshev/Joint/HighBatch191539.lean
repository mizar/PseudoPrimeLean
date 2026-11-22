/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 191539 to 196539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e191539 : Edge :=
  ⟨191539, 191558662826644864, 191560257013900818, 495795475751650, 495801405654795⟩

private def e196539 : Edge :=
  ⟨196539, 196526302637460001, 196527934662644933, 507973543428502, 507979627855476⟩

private def extra191539 : ℕ → ℕ
  | 191539 => 321
  | 191861 => 329
  | 192191 => 347
  | 192539 => 293
  | 192833 => 239
  | 193073 => 299
  | 193373 => 275
  | 193649 => 233
  | 193883 => 229
  | 194113 => 329
  | 194443 => 365
  | 194809 => 321
  | 195131 => 295
  | 195427 => 333
  | 195761 => 311
  | 196073 => 355
  | 196429 => 109
  | _ => 0

private theorem part191539 : Segment Valid highEstimate e191539 e196539 := by
  apply gcd_batch (by decide) (by decide) extra191539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [191539,196539). -/
theorem batch191539 :
    Segment Valid highEstimate
      ⟨191539, 191558662826644864, 191560257013900818, 495795475751650, 495801405654795⟩
      ⟨196539, 196526302637460001, 196527934662644933, 507973543428502, 507979627855476⟩ := by
  exact part191539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
