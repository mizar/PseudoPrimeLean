/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 326539 to 331539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e326539 : Edge :=
  ⟨326539, 326618065632642258, 326620662106426693, 642526791887481, 642534922671444⟩

private def e331539 : Edge :=
  ⟨331539, 331725008061551196, 331727639643786108, 642526791887481, 642534922671444⟩

private def extra326539 : ℕ → ℕ
  | 326539 => 341
  | 326881 => 369
  | 327251 => 301
  | 327553 => 273
  | 327827 => 239
  | 328067 => 263
  | 328331 => 289
  | 328621 => 297
  | 328919 => 337
  | 329257 => 333
  | 329591 => 307
  | 329899 => 299
  | 330199 => 233
  | 330433 => 269
  | 330703 => 279
  | 330983 => 275
  | 331259 => 277
  | 331537 => 1
  | _ => 0

private theorem part326539 : Segment Valid highEstimate e326539 e331539 := by
  apply gcd_batch (by decide) (by decide) extra326539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [326539,331539). -/
theorem batch326539 :
    Segment Valid highEstimate
      ⟨326539, 326618065632642258, 326620662106426693, 642526791887481, 642534922671444⟩
      ⟨331539, 331725008061551196, 331727639643786108, 642526791887481, 642534922671444⟩ := by
  exact part326539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
