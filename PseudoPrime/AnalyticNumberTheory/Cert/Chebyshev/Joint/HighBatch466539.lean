/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 466539 to 471539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e466539 : Edge :=
  ⟨466539, 466250265461667456, 466253696779499100, 777716877009608, 777726748583835⟩

private def e471539 : Edge :=
  ⟨471539, 471434476897369183, 471437918336622150, 777716877009608, 777726748583835⟩

private def extra466539 : ℕ → ℕ
  | 466539 => 256
  | 466796 => 261
  | 467058 => 194
  | 467253 => 195
  | 467449 => 169
  | 467619 => 221
  | 467841 => 274
  | 468116 => 325
  | 468442 => 300
  | 468743 => 391
  | 469135 => 351
  | 469487 => 352
  | 469840 => 339
  | 470180 => 339
  | 470520 => 417
  | 470938 => 456
  | 471395 => 143
  | _ => 0

private theorem part466539 : Segment Valid highEstimate e466539 e471539 := by
  apply gcd_batch (by decide) (by decide) extra466539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [466539,471539). -/
theorem batch466539 :
    Segment Valid highEstimate
      ⟨466539, 466250265461667456, 466253696779499100, 777716877009608, 777726748583835⟩
      ⟨471539, 471434476897369183, 471437918336622150, 777716877009608, 777726748583835⟩ := by
  exact part466539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
