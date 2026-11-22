/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.ThetaEntry

/-! # Joint prefix verification from 2657 through 2658 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def extra : ℕ → ℕ
  | 2657 => 1
  | _ => 0

private def entry : Edge :=
  ⟨2657, 2624016843000490, 2624050214203841, 64765146252886, 64765146253001⟩

private def stop : Edge :=
  ⟨2659, 2631901795289406, 2631935245573419, 64765146252886, 64765146253001⟩

private theorem checked : batchAccepted 2657 2659 extra (fun _ ↦ (4, 5)) 1 entry stop = true := by
  decide +kernel

/-- Both finite estimates on the first real theta cell follow from
the checked entry prefix and the two integer updates. -/
theorem first_joint_segment :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x)
      ⟨2657, 2624016843000490, 2624050214203841, 64765146252886, 64765146253001⟩
      ⟨2659, 2631901795289406, 2631935245573419, 64765146252886, 64765146253001⟩ := by
  apply accepted_segment (by decide) _ checked
  intro n x ha hb _ _ h
  have hn : n < 3100 := by linarith only [hb, Nat.zero_le (extra n)]
  exact ⟨h.1, by simpa only [thetaBand, ite_eq_left hn, Nat.cast_ofNat] using h.2 ha le_rfl⟩

/-- The initial prefix reaches the first theta cell and certifies both real estimates. -/
theorem first_joint :
    Valid ⟨2659, 2631901795289406, 2631935245573419, 64765146252886, 64765146253001⟩ ∧
      ∀ x : ℝ,
        2657 ≤ x →
          x < 2659 →
          |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
            |Chebyshev.theta x - x| ≤ (9 / 5 : ℝ) * Real.sqrt x := by
  exact first_joint_segment theta_entry.1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
