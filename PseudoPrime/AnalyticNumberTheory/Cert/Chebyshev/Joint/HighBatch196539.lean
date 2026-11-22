/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 196539 to 201539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e196539 : Edge :=
  ⟨196539, 196526302637460001, 196527934662644933, 507973543428502, 507979627855476⟩

private def e201539 : Edge :=
  ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩

private def extra196539 : ℕ → ℕ
  | 196539 => 339
  | 196879 => 363
  | 197243 => 329
  | 197573 => 335
  | 197909 => 331
  | 198241 => 291
  | 198533 => 299
  | 198833 => 317
  | 199151 => 335
  | 199487 => 319
  | 199807 => 345
  | 200153 => 313
  | 200467 => 401
  | 200869 => 321
  | 201191 => 305
  | 201497 => 41
  | _ => 0

private theorem part196539 : Segment Valid highEstimate e196539 e201539 := by
  apply gcd_batch (by decide) (by decide) extra196539 16
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [196539,201539). -/
theorem batch196539 :
    Segment Valid highEstimate
      ⟨196539, 196526302637460001, 196527934662644933, 507973543428502, 507979627855476⟩
      ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩ := by
  exact part196539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
