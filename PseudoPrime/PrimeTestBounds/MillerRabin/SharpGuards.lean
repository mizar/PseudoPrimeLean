/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularProfiles

/-! # Guarded numerical assembly of the sharp witness candidates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A triangular candidate is active only above its certified entrance.
The supplied base is the fallback for every inactive profile. -/
noncomputable def sharpHighGuard (L B : ℝ) (i : Fin 8) : ℝ :=
  if (Analysis.triangularProfile i).T ≤ L then (Analysis.triangularProfile i).C * L ^ 2 else B

/-- The minimum of the base and the eight guarded triangular candidates.
Every profile retains its own exact certified entrance. -/
noncomputable def sharpHighMin (L B : ℝ) : ℝ :=
  min B
    (min (sharpHighGuard L B 0)
      (min (sharpHighGuard L B 1)
        (min (sharpHighGuard L B 2)
          (min (sharpHighGuard L B 3)
            (min (sharpHighGuard L B 4)
              (min (sharpHighGuard L B 5) (min (sharpHighGuard L B 6) (sharpHighGuard L B 7))))))))

/-- A common lower bound for the base and every active triangular candidate
bounds their guarded minimum. Resolve each guard before combining the inequalities. -/
theorem sharpHigh_lower {L B C : ℝ} (hB : C ≤ B)
    (hH :
      ∀ i : Fin 8,
        (Analysis.triangularProfile i).T ≤ L → C ≤ (Analysis.triangularProfile i).C * L ^ 2) :
    C ≤ sharpHighMin L B := by
  have hg (i : Fin 8) : C ≤ sharpHighGuard L B i := by
    by_cases hi : (Analysis.triangularProfile i).T ≤ L
    · simpa only [sharpHighGuard, ite_eq_left hi] using hH i hi
    · simpa only [sharpHighGuard, ite_eq_right hi] using hB
  exact
    le_min hB
      (le_min (hg 0)
        (le_min (hg 1)
          (le_min (hg 2) (le_min (hg 3) (le_min (hg 4) (le_min (hg 5) (le_min (hg 6) (hg 7))))))))

/-- The guarded triangular minimum never exceeds its supplied base. -/
theorem sharpHigh_le_base (L B : ℝ) : sharpHighMin L B ≤ B :=
  min_le_left _ _

/-- At a certified entrance, the guarded triangular minimum is below that profile.
Project the corresponding one of the eight finite minimum branches. -/
theorem sharpHigh_le_profile (L B : ℝ) (i : Fin 8) (hi : (Analysis.triangularProfile i).T ≤ L) :
    sharpHighMin L B ≤ (Analysis.triangularProfile i).C * L ^ 2 := by
  have hg : sharpHighMin L B ≤ sharpHighGuard L B i := by
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    · exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    · exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    · exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
    · exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))))
  simpa only [sharpHighGuard, ite_eq_left hi] using hg

/-- Below thirty billion all eight triangular guards are inactive.
Their common certified entrance lower bound reduces the minimum to its base. -/
theorem sharpHigh_eq_base {L B : ℝ} (hL : L < 30000000000) : sharpHighMin L B = B := by
  have hi (i : Fin 8) : ¬(Analysis.triangularProfile i).T ≤ L := by
    linarith only [(Analysis.triangularProfile i).entry, hL]
  simp only [sharpHighMin, sharpHighGuard, ite_eq_right (hi _), min_self]

/-- Combine a base, two analytic candidates guarded at scale 63, and the high minimum.
Inactive analytic candidates use the base as fallback. -/
noncomputable def sharpGuardMin (L B G S H : ℝ) : ℝ :=
  min B (min (if 63 ≤ L then G else B) (min (if 63 ≤ L then S else B) H))

/-- The exact two-region form of the analytic guard minimum.
The high part keeps its own independently certified triangular entrances. -/
noncomputable def sharpGuardSelected (L B G S H : ℝ) : ℝ :=
  if L < 63 then min B H else min B (min G (min S H))

/-- The guarded and selected scalar assemblies agree for arbitrary real candidates.
Split only at scale 63 and remove repeated base minima. -/
theorem sharpGuardMin_eq_selected (L B G S H : ℝ) :
    sharpGuardMin L B G S H = sharpGuardSelected L B G S H := by
  by_cases hL : L < 63
  · simp only [sharpGuardMin, sharpGuardSelected, ite_eq_left hL, ite_eq_right (not_le.mpr hL),
      ← min_assoc, min_self]
  · simp only [sharpGuardMin, sharpGuardSelected, ite_eq_right hL, ite_eq_left (le_of_not_gt hL)]

/-- A lower bound for the base, both valid analytic candidates and the high part
bounds their guarded scalar assembly. This transfers actual least-prime bounds. -/
theorem sharpGuard_lower {L B G S H C : ℝ} (hB : C ≤ B) (hG : 63 ≤ L → C ≤ G) (hS : 63 ≤ L → C ≤ S)
    (hH : C ≤ H) : C ≤ sharpGuardMin L B G S H := by
  have hg {X : ℝ} (hX : 63 ≤ L → C ≤ X) : C ≤ if 63 ≤ L then X else B := by
    by_cases h : 63 ≤ L
    · rw [ite_eq_left h]; exact hX h
    · rw [ite_eq_right h]; exact hB
  exact le_min hB (le_min (hg hG) (le_min (hg hS) hH))

/-- If an active profile has the smallest valid coefficient, the high minimum is exactly
its cutoff intersected with the base. The proof compares every active branch directly. -/
theorem sharpHigh_eq_active {L B : ℝ} (i : Fin 8) (hi : (Analysis.triangularProfile i).T ≤ L)
    (hbest :
      ∀ j : Fin 8,
        (Analysis.triangularProfile j).T ≤ L →
          (Analysis.triangularProfile i).C ≤ (Analysis.triangularProfile j).C) :
    sharpHighMin L B = min B ((Analysis.triangularProfile i).C * L ^ 2) := by
  apply le_antisymm
  · exact le_min (sharpHigh_le_base L B) (sharpHigh_le_profile L B i hi)
  · apply sharpHigh_lower (min_le_left _ _)
    intro j hj
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (hbest j hj) (sq_nonneg L))

end PseudoPrime.PrimeTestBounds.MillerRabin
