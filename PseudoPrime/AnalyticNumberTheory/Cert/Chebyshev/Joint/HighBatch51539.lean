/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 51539 to 56539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e51539 : Edge :=
  ⟨51539, 51522757957835874, 51523239117218398, 262975175719775, 262977893348012⟩

private def e56539 : Edge :=
  ⟨56539, 56557371116941355, 56557880493476111, 273859936122240, 273862672658375⟩

private def extra51539 : ℕ → ℕ
  | 51539 => 171
  | 51711 => 174
  | 51886 => 180
  | 52067 => 181
  | 52249 => 181
  | 52431 => 152
  | 52584 => 173
  | 52758 => 163
  | 52922 => 152
  | 53075 => 141
  | 53217 => 174
  | 53392 => 163
  | 53556 => 141
  | 53698 => 163
  | 53862 => 163
  | 54026 => 174
  | 54201 => 152
  | 54354 => 120
  | 54475 => 152
  | 54628 => 185
  | 54814 => 174
  | 54989 => 164
  | 55154 => 152
  | 55307 => 131
  | 55439 => 130
  | 55570 => 98
  | 55669 => 131
  | 55801 => 131
  | 55933 => 196
  | 56130 => 175
  | 56306 => 164
  | 56471 => 67
  | _ => 0

private theorem part51539 : Segment Valid highEstimate e51539 e56539 := by
  apply gcd_batch (by decide) (by decide) extra51539 32
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [51539,56539). -/
theorem batch51539 :
    Segment Valid highEstimate
      ⟨51539, 51522757957835874, 51523239117218398, 262975175719775, 262977893348012⟩
      ⟨56539, 56557371116941355, 56557880493476111, 273859936122240, 273862672658375⟩ := by
  exact part51539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
