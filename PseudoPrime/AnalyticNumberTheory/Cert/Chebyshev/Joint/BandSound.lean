/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BatchSound

/-! # Checked cells contained within one theta coefficient band -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- A successful replay gives both real bounds whenever the theta coefficient is constant
between the two batch cursors and the batch starts at or above 2657. -/
theorem accepted_band {a b : ℕ} (hu : b ≤ 1000001) (hl : 2657 ≤ a) (u v : ℕ)
    (band : ∀ n, a ≤ n → n < b → thetaBand n = (u, v)) (extra : ℕ → ℕ) (count : ℕ) {s t : Edge}
    (hg : batchAccepted a b extra (fun _ ↦ (4, 5)) count s t = true) :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ ((u : ℝ) / v) * Real.sqrt x)
      s t := by
  apply accepted_segment hu _ hg
  intro n x ha hb _ _ h
  have hn : n < b := by linarith only [hb, Nat.zero_le (extra n)]
  exact ⟨h.1, by simpa only [band n ha hn] using h.2 (hl.trans ha) le_rfl⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
