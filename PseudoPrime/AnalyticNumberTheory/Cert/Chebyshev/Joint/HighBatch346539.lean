/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 346539 to 351539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e346539 : Edge :=
  ⟨346539, 346700011368420178, 346702767638907207, 655259656683198, 655267971326173⟩

private def e351539 : Edge :=
  ⟨351539, 351754154763738223, 351756956336323203, 655259656683198, 655267971326173⟩

private def extra346539 : ℕ → ℕ
  | 346539 => 327
  | 346867 => 299
  | 347167 => 341
  | 347509 => 339
  | 347849 => 313
  | 348163 => 279
  | 348443 => 295
  | 348739 => 311
  | 349051 => 327
  | 349379 => 317
  | 349697 => 251
  | 349949 => 299
  | 350249 => 343
  | 350593 => 305
  | 350899 => 279
  | 351179 => 247
  | 351427 => 111
  | _ => 0

private theorem part346539 : Segment Valid highEstimate e346539 e351539 := by
  apply gcd_batch (by decide) (by decide) extra346539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [346539,351539). -/
theorem batch346539 :
    Segment Valid highEstimate
      ⟨346539, 346700011368420178, 346702767638907207, 655259656683198, 655267971326173⟩
      ⟨351539, 351754154763738223, 351756956336323203, 655259656683198, 655267971326173⟩ := by
  exact part346539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
