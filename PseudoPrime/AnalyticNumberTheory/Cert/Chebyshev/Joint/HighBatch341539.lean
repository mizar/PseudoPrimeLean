/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 341539 to 346539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e341539 : Edge :=
  ⟨341539, 341645214124329997, 341647926002239681, 648884634152238, 648892766443253⟩

private def e346539 : Edge :=
  ⟨346539, 346700011368420178, 346702767638907207, 655259656683198, 655267971326173⟩

private def extra341539 : ℕ → ℕ
  | 341539 => 371
  | 341911 => 329
  | 342241 => 311
  | 342553 => 317
  | 342871 => 381
  | 343253 => 335
  | 343589 => 349
  | 343939 => 311
  | 344251 => 359
  | 344611 => 329
  | 344941 => 365
  | 345307 => 381
  | 345689 => 361
  | 346051 => 339
  | 346391 => 147
  | _ => 0

private theorem part341539 : Segment Valid highEstimate e341539 e346539 := by
  apply gcd_batch (by decide) (by decide) extra341539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [341539,346539). -/
theorem batch341539 :
    Segment Valid highEstimate
      ⟨341539, 341645214124329997, 341647926002239681, 648884634152238, 648892766443253⟩
      ⟨346539, 346700011368420178, 346702767638907207, 655259656683198, 655267971326173⟩ := by
  exact part341539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
