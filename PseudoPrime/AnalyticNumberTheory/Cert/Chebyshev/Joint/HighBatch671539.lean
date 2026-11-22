/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 671539 to 676539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e671539 : Edge :=
  ⟨671539, 671325556054094871, 671330641003367806, 900855262095811, 900866620298927⟩

private def e676539 : Edge :=
  ⟨676539, 676351726654129048, 676356818643495776, 907565785128918, 907577162104873⟩

private def extra671539 : ℕ → ℕ
  | 671539 => 441
  | 671981 => 442
  | 672424 => 482
  | 672907 => 442
  | 673350 => 483
  | 673834 => 536
  | 674371 => 489
  | 674861 => 496
  | 675358 => 509
  | 675868 => 482
  | 676351 => 187
  | _ => 0

private theorem part671539 : Segment Valid highEstimate e671539 e676539 := by
  apply gcd_batch (by decide) (by decide) extra671539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [671539,676539). -/
theorem batch671539 :
    Segment Valid highEstimate
      ⟨671539, 671325556054094871, 671330641003367806, 900855262095811, 900866620298927⟩
      ⟨676539, 676351726654129048, 676356818643495776, 907565785128918, 907577162104873⟩ := by
  exact part671539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
