/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 451539 to 456539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e451539 : Edge :=
  ⟨451539, 451642371235837931, 451645740542203779, 758160967129436, 758170675943213⟩

private def e456539 : Edge :=
  ⟨456539, 456442439456991137, 456445821762249399, 764672712457974, 764682422378976⟩

private def extra451539 : ℕ → ℕ
  | 451539 => 369
  | 451909 => 383
  | 452293 => 503
  | 452797 => 531
  | 453329 => 550
  | 453880 => 468
  | 454349 => 469
  | 454819 => 416
  | 455236 => 429
  | 455666 => 507
  | 456174 => 364
  | _ => 0

private theorem part451539 : Segment Valid highEstimate e451539 e456539 := by
  apply gcd_batch (by decide) (by decide) extra451539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [451539,456539). -/
theorem batch451539 :
    Segment Valid highEstimate
      ⟨451539, 451642371235837931, 451645740542203779, 758160967129436, 758170675943213⟩
      ⟨456539, 456442439456991137, 456445821762249399, 764672712457974, 764682422378976⟩ := by
  exact part451539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
