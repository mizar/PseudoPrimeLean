/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 616539 to 621539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e616539 : Edge :=
  ⟨616539, 616861142645614799, 616865721992786208, 874112115045486, 874123170639620⟩

private def e621539 : Edge :=
  ⟨621539, 621815422073023980, 621820085293590167, 880780343275270, 880791406190584⟩

private def extra616539 : ℕ → ℕ
  | 616539 => 303
  | 616843 => 285
  | 617129 => 233
  | 617363 => 283
  | 617647 => 195
  | 617843 => 209
  | 618053 => 269
  | 618323 => 263
  | 618587 => 325
  | 618913 => 293
  | 619207 => 375
  | 619583 => 337
  | 619921 => 375
  | 620297 => 341
  | 620639 => 307
  | 620947 => 341
  | 621289 => 249
  | _ => 0

private theorem part616539 : Segment Valid highEstimate e616539 e621539 := by
  apply gcd_batch (by decide) (by decide) extra616539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [616539,621539). -/
theorem batch616539 :
    Segment Valid highEstimate
      ⟨616539, 616861142645614799, 616865721992786208, 874112115045486, 874123170639620⟩
      ⟨621539, 621815422073023980, 621820085293590167, 880780343275270, 880791406190584⟩ := by
  exact part616539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
