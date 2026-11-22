/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 251539 to 256539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e251539 : Edge :=
  ⟨251539, 251645861104826777, 251647743667137801, 571580126340599, 571586668000734⟩

private def e256539 : Edge :=
  ⟨256539, 256605331295637934, 256607231429693859, 577800715583523, 577807356830686⟩

private def extra251539 : ℕ → ℕ
  | 251539 => 321
  | 251861 => 311
  | 252173 => 289
  | 252463 => 359
  | 252823 => 419
  | 253243 => 387
  | 253631 => 337
  | 253969 => 329
  | 254299 => 447
  | 254747 => 359
  | 255107 => 349
  | 255457 => 309
  | 255767 => 289
  | 256057 => 311
  | 256369 => 169
  | _ => 0

private theorem part251539 : Segment Valid highEstimate e251539 e256539 := by
  apply gcd_batch (by decide) (by decide) extra251539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [251539,256539). -/
theorem batch251539 :
    Segment Valid highEstimate
      ⟨251539, 251645861104826777, 251647743667137801, 571580126340599, 571586668000734⟩
      ⟨256539, 256605331295637934, 256607231429693859, 577800715583523, 577807356830686⟩ := by
  exact part251539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
