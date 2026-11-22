/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 261539 to 266539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e261539 : Edge :=
  ⟨261539, 261447865457459711, 261449783722830360, 584033163277008, 584039853733679⟩

private def e266539 : Edge :=
  ⟨266539, 266454596163441081, 266456536110049775, 584726310457567, 584733000914240⟩

private def extra261539 : ℕ → ℕ
  | 261539 => 316
  | 261856 => 324
  | 262181 => 299
  | 262481 => 287
  | 262769 => 324
  | 263094 => 273
  | 263368 => 262
  | 263631 => 323
  | 263955 => 337
  | 264293 => 324
  | 264618 => 273
  | 264892 => 299
  | 265192 => 312
  | 265505 => 311
  | 265817 => 312
  | 266130 => 374
  | 266505 => 33
  | _ => 0

private theorem part261539 : Segment Valid highEstimate e261539 e266539 := by
  apply gcd_batch (by decide) (by decide) extra261539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [261539,266539). -/
theorem batch261539 :
    Segment Valid highEstimate
      ⟨261539, 261447865457459711, 261449783722830360, 584033163277008, 584039853733679⟩
      ⟨266539, 266454596163441081, 266456536110049775, 584726310457567, 584733000914240⟩ := by
  exact part261539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
