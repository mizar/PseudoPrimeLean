/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseGrowth

/-! # Monotonicity of pointwise cutoffs and upper-cap fixed-prime guards -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The inverse pointwise cutoff increases on all real logarithmic levels.
Its radius is always at least eight; squaring therefore preserves radius monotonicity. -/
theorem pointwiseCutoff_mono : Monotone pointwiseCutoff := by
  intro L K hLK
  have hL := (pointwiseRadius_spec L).1
  have hK := (pointwiseRadius_spec K).1
  exact
    (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ pointwiseRadius L)
          (by linarith only [hK] : (0 : ℝ) ≤ pointwiseRadius K)).mpr
      (pointwiseRadius_mono hLK)

/-- A fixed-prime candidate is valid through its upper cap.
Outside the cap, it yields the pointwise base. -/
noncomputable def upperGuardPointwise (cap b L : ℝ) : ℝ :=
  if L ≤ cap then min b (pointwiseCutoff L) else pointwiseCutoff L

/-- Upper-cap fixed-prime guards preserve monotonicity of the pointwise base.
Crossing the cap only removes a minimum with a constant, so it cannot lower the value. -/
theorem upperGuardPointwise_mono (cap b : ℝ) : Monotone (upperGuardPointwise cap b) := by
  intro L K hLK
  have hp := pointwiseCutoff_mono hLK
  by_cases hL : L ≤ cap
  · by_cases hK : K ≤ cap
    · rw [upperGuardPointwise, upperGuardPointwise, ite_eq_left hL, ite_eq_left hK]
      exact le_min (min_le_left _ _) ((min_le_right _ _).trans hp)
    · rw [upperGuardPointwise, upperGuardPointwise, ite_eq_left hL, ite_eq_right hK]
      exact (min_le_right _ _).trans hp
  · have hK : ¬K ≤ cap := fun h ↦ hL (hLK.trans h)
    rw [upperGuardPointwise, upperGuardPointwise, ite_eq_right hL, ite_eq_right hK]
    exact hp

/-- Extending the upper cap can only decrease the guarded pointwise candidate. -/
theorem upperGuardPointwise_antitone_cap {c d : ℝ} (hcd : c ≤ d) (b L : ℝ) :
    upperGuardPointwise d b L ≤ upperGuardPointwise c b L := by
  by_cases hL : L ≤ c
  · have hd : L ≤ d := hL.trans hcd
    rw [upperGuardPointwise, upperGuardPointwise, ite_eq_left hL, ite_eq_left hd]
  · by_cases hd : L ≤ d
    · rw [upperGuardPointwise, upperGuardPointwise, ite_eq_right hL, ite_eq_left hd]
      exact min_le_right _ _
    · rw [upperGuardPointwise, upperGuardPointwise, ite_eq_right hL, ite_eq_right hd]

end PseudoPrime.LLS.PaperStatements
