/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 176539 to 181539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e176539 : Edge :=
  ⟨176539, 176458855475595456, 176460348802168409, 476517386870567, 476523105582838⟩

private def e181539 : Edge :=
  ⟨181539, 181400821236517595, 181402347797528581, 483658631419302, 483664422362539⟩

private def extra176539 : ℕ → ℕ
  | 176539 => 255
  | 176795 => 277
  | 177073 => 265
  | 177339 => 245
  | 177585 => 205
  | 177791 => 156
  | 177948 => 169
  | 178118 => 169
  | 178288 => 156
  | 178445 => 169
  | 178615 => 217
  | 178833 => 217
  | 179051 => 254
  | 179306 => 241
  | 179548 => 278
  | 179827 => 309
  | 180137 => 281
  | 180419 => 331
  | 180751 => 347
  | 181099 => 254
  | 181354 => 184
  | _ => 0

private theorem part176539 : Segment Valid highEstimate e176539 e181539 := by
  apply gcd_batch (by decide) (by decide) extra176539 21
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [176539,181539). -/
theorem batch176539 :
    Segment Valid highEstimate
      ⟨176539, 176458855475595456, 176460348802168409, 476517386870567, 476523105582838⟩
      ⟨181539, 181400821236517595, 181402347797528581, 483658631419302, 483664422362539⟩ := by
  exact part176539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
