/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Psi11To17
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Psi17To101

/-! # Initial joint bounds through the cursor at 101 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem warm_valid :
    Valid ⟨11, 7832014180496, 7832014180512, 2484906649785, 2484906649791⟩ := by
  have hs :=
    (walk_valid (a := 1) (b := 11) 10 _ initial_valid (by decide) (by decide) (by decide)).2
  have he :
    walk (segmentStep 1 11) 10 ⟨1, 0, 0, 0, 0⟩ =
      ⟨11, 7832014180496, 7832014180512, 2484906649785, 2484906649791⟩ := by
    decide +kernel
  exact he ▸ hs

/-- Real psi estimates before 101 and the outgoing four-tick invariant, starting at one. -/
theorem low_prefix :
    Valid ⟨101, 94045306083764, 94045894722428, 10316920830281, 10316920830303⟩ ∧
      (∀ x : ℝ, 11 ≤ x → x < 17 → |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x) ∧
      (∀ x : ℝ, 17 ≤ x → x < 101 → |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x) := by
  obtain ⟨hs, hfirst⟩ := psiSegment11To17 warm_valid
  obtain ⟨ht, hsecond⟩ := psiSegment17To101 hs
  exact ⟨ht, hfirst, hsecond⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
