/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 291539 to 296539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e291539 : Edge :=
  ⟨291539, 291509441890940974, 291511685352571087, 600377131139129, 600384206880252⟩

private def e296539 : Edge :=
  ⟨296539, 296300504889641223, 296302817040882213, 606670545532904, 606677924376081⟩

private def extra291539 : ℕ → ℕ
  | 291539 => 414
  | 291954 => 364
  | 292319 => 352
  | 292672 => 339
  | 293012 => 345
  | 293358 => 339
  | 293698 => 264
  | 293963 => 213
  | 294177 => 226
  | 294404 => 314
  | 294719 => 226
  | 294946 => 251
  | 295198 => 251
  | 295450 => 276
  | 295727 => 176
  | 295904 => 226
  | 296131 => 226
  | 296358 => 180
  | _ => 0

private theorem part291539 : Segment Valid highEstimate e291539 e296539 := by
  apply gcd_batch (by decide) (by decide) extra291539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [291539,296539). -/
theorem batch291539 :
    Segment Valid highEstimate
      ⟨291539, 291509441890940974, 291511685352571087, 600377131139129, 600384206880252⟩
      ⟨296539, 296300504889641223, 296302817040882213, 606670545532904, 606677924376081⟩ := by
  exact part291539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
