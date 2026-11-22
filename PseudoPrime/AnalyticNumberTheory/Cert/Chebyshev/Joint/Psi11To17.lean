/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BatchSound

/-! # Joint prefix verification from 11 through 16 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def extra : ℕ → ℕ
  | 11 => 1
  | 13 => 2
  | _ => 0

private def entry : Edge :=
  ⟨11, 7832014180496, 7832014180512, 2484906649785, 2484906649791⟩

private def stop : Edge :=
  ⟨17, 13488005991308, 13488005991334, 3178053830344, 3178053830352⟩

private theorem checked : batchAccepted 11 17 extra (fun _ ↦ (47, 50)) 3 entry stop = true := by
  decide +kernel

/-- From a certified entry at 11, the checked cells give a certified exit at 17
and the psi estimate at every real point between the two cursors. -/
theorem psiSegment11To17 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x)
      ⟨11, 7832014180496, 7832014180512, 2484906649785, 2484906649791⟩
      ⟨17, 13488005991308, 13488005991334, 3178053830344, 3178053830352⟩ := by
  exact accepted_segment (by decide) (fun _ _ _ _ _ _ h ↦ h.1) checked

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
