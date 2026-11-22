/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 651539 to 656539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e651539 : Edge :=
  ⟨651539, 651316027203783601, 651320913964596621, 887461196452993, 887472396843589⟩

private def e656539 : Edge :=
  ⟨656539, 656330909011565733, 656335872066887132, 894156994899402, 894168258571258⟩

private def extra651539 : ℕ → ℕ
  | 651539 => 421
  | 651961 => 401
  | 652363 => 401
  | 652765 => 495
  | 653261 => 441
  | 653703 => 414
  | 654118 => 468
  | 654587 => 488
  | 655076 => 535
  | 655612 => 562
  | 656175 => 363
  | _ => 0

private theorem part651539 : Segment Valid highEstimate e651539 e656539 := by
  apply gcd_batch (by decide) (by decide) extra651539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [651539,656539). -/
theorem batch651539 :
    Segment Valid highEstimate
      ⟨651539, 651316027203783601, 651320913964596621, 887461196452993, 887472396843589⟩
      ⟨656539, 656330909011565733, 656335872066887132, 894156994899402, 894168258571258⟩ := by
  exact part651539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
