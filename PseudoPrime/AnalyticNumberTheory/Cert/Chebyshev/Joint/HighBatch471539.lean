/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 471539 to 476539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e471539 : Edge :=
  ⟨471539, 471434476897369183, 471437918336622150, 777716877009608, 777726748583835⟩

private def e476539 : Edge :=
  ⟨476539, 476622914592591850, 476626382889250586, 777716877009608, 777726748583835⟩

private def extra471539 : ℕ → ℕ
  | 471539 => 457
  | 471997 => 495
  | 472493 => 496
  | 472990 => 444
  | 473435 => 417
  | 473853 => 404
  | 474258 => 470
  | 474729 => 483
  | 475213 => 483
  | 475697 => 413
  | 476111 => 427
  | _ => 0

private theorem part471539 : Segment Valid highEstimate e471539 e476539 := by
  apply gcd_batch (by decide) (by decide) extra471539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [471539,476539). -/
theorem batch471539 :
    Segment Valid highEstimate
      ⟨471539, 471434476897369183, 471437918336622150, 777716877009608, 777726748583835⟩
      ⟨476539, 476622914592591850, 476626382889250586, 777716877009608, 777726748583835⟩ := by
  exact part471539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
