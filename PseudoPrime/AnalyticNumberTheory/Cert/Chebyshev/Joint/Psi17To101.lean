/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BatchSound

/-! # Joint prefix verification from 17 through 100 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def extra : ℕ → ℕ
  | 17 => 1
  | 19 => 3
  | 23 => 2
  | 26 => 1
  | 29 => 3
  | 33 => 3
  | 37 => 3
  | 41 => 3
  | 45 => 3
  | 49 => 5
  | 55 => 3
  | 59 => 4
  | 64 => 4
  | 69 => 3
  | 73 => 7
  | 81 => 6
  | 88 => 3
  | 92 => 4
  | 97 => 3
  | _ => 0

private def entry : Edge :=
  ⟨17, 13488005991308, 13488005991334, 3178053830344, 3178053830352⟩

private def stop : Edge :=
  ⟨101, 94045306083764, 94045894722428, 10316920830281, 10316920830303⟩

private theorem checked : batchAccepted 17 101 extra (fun _ ↦ (81, 100)) 20 entry stop = true := by
  decide +kernel

/-- From a certified entry at 17, the checked cells give a certified exit at 101
and the psi estimate at every real point between the two cursors. -/
theorem psiSegment17To101 :
    Segment Valid (fun x ↦ |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x)
      ⟨17, 13488005991308, 13488005991334, 3178053830344, 3178053830352⟩
      ⟨101, 94045306083764, 94045894722428, 10316920830281, 10316920830303⟩ := by
  exact accepted_segment (by decide) (fun _ _ _ _ _ _ h ↦ h.1) checked

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
