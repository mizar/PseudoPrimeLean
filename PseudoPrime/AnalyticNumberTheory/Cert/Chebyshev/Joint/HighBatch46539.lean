/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 46539 to 51539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e46539 : Edge :=
  ⟨46539, 46486299092317656, 46486745158536790, 248532137647683, 248534672616378⟩

private def e51539 : Edge :=
  ⟨51539, 51522757957835874, 51523239117218398, 262975175719775, 262977893348012⟩

private def extra46539 : ℕ → ℕ
  | 46539 => 116
  | 46656 => 129
  | 46786 => 139
  | 46926 => 140
  | 47067 => 96
  | 47164 => 118
  | 47283 => 75
  | 47359 => 96
  | 47456 => 96
  | 47553 => 107
  | 47661 => 129
  | 47791 => 128
  | 47920 => 129
  | 48050 => 128
  | 48179 => 107
  | 48287 => 96
  | 48384 => 86
  | 48471 => 74
  | 48546 => 118
  | 48665 => 108
  | 48774 => 96
  | 48871 => 139
  | 49011 => 108
  | 49120 => 118
  | 49239 => 139
  | 49379 => 129
  | 49509 => 140
  | 49650 => 140
  | 49791 => 156
  | 49948 => 170
  | 50119 => 171
  | 50291 => 169
  | 50461 => 189
  | 50651 => 174
  | 50826 => 122
  | 50949 => 119
  | 51069 => 129
  | 51199 => 118
  | 51318 => 108
  | 51427 => 111
  | _ => 0

private theorem part46539 : Segment Valid highEstimate e46539 e51539 := by
  apply gcd_batch (by decide) (by decide) extra46539 40
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [46539,51539). -/
theorem batch46539 :
    Segment Valid highEstimate
      ⟨46539, 46486299092317656, 46486745158536790, 248532137647683, 248534672616378⟩
      ⟨51539, 51522757957835874, 51523239117218398, 262975175719775, 262977893348012⟩ := by
  exact part46539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
