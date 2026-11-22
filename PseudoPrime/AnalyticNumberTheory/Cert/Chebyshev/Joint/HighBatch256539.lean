/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 256539 to 261539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e256539 : Edge :=
  ⟨256539, 256605331295637934, 256607231429693859, 577800715583523, 577807356830686⟩

private def e261539 : Edge :=
  ⟨261539, 261447865457459711, 261449783722830360, 584033163277008, 584039853733679⟩

private def extra256539 : ℕ → ℕ
  | 256539 => 391
  | 256931 => 407
  | 257339 => 406
  | 257746 => 398
  | 258145 => 398
  | 258544 => 374
  | 258919 => 389
  | 259309 => 387
  | 259697 => 413
  | 260111 => 407
  | 260519 => 349
  | 260869 => 361
  | 261231 => 307
  | _ => 0

private theorem part256539 : Segment Valid highEstimate e256539 e261539 := by
  apply gcd_batch (by decide) (by decide) extra256539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [256539,261539). -/
theorem batch256539 :
    Segment Valid highEstimate
      ⟨256539, 256605331295637934, 256607231429693859, 577800715583523, 577807356830686⟩
      ⟨261539, 261447865457459711, 261449783722830360, 584033163277008, 584039853733679⟩ := by
  exact part256539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
