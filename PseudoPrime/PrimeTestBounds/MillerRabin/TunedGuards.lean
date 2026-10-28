/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedBounds

/-! # Guards for the seven tuned high-range profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A tuned triangular cutoff is active at its certified entrance; otherwise use the base. -/
noncomputable def tunedHighGuard (L B : ℝ) (i : Fin 7) : ℝ :=
  if (Analysis.triangularTunedProfile i).T ≤ L then (Analysis.triangularTunedProfile i).C * L ^ 2
  else B

/-- Intersect the base with all seven certified high-range cutoffs. -/
noncomputable def tunedHighMin (L B : ℝ) : ℝ :=
  min B
    (min (tunedHighGuard L B 0)
      (min (tunedHighGuard L B 1)
        (min (tunedHighGuard L B 2)
          (min (tunedHighGuard L B 3)
            (min (tunedHighGuard L B 4) (min (tunedHighGuard L B 5) (tunedHighGuard L B 6)))))))

/-- A common lower bound for the base and all active profiles bounds their guarded minimum. -/
theorem tunedHigh_lower {L B C : ℝ} (hB : C ≤ B)
    (hH :
      ∀ i : Fin 7,
        (Analysis.triangularTunedProfile i).T ≤ L →
          C ≤ (Analysis.triangularTunedProfile i).C * L ^ 2) :
    C ≤ tunedHighMin L B := by
  have hg (i : Fin 7) : C ≤ tunedHighGuard L B i := by
    by_cases hi : (Analysis.triangularTunedProfile i).T ≤ L
    · simpa only [tunedHighGuard, ite_eq_left hi] using hH i hi
    · simpa only [tunedHighGuard, ite_eq_right hi] using hB
  exact
    le_min hB
      (le_min (hg 0)
        (le_min (hg 1) (le_min (hg 2) (le_min (hg 3) (le_min (hg 4) (le_min (hg 5) (hg 6)))))))

/-- Above a certified entrance the guarded minimum is below the corresponding profile. -/
theorem tunedHigh_le_profile (L B : ℝ) (i : Fin 7)
    (hi : (Analysis.triangularTunedProfile i).T ≤ L) :
    tunedHighMin L B ≤ (Analysis.triangularTunedProfile i).C * L ^ 2 := by
  have hg : tunedHighMin L B ≤ tunedHighGuard L B i := by
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
                ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  simpa only [tunedHighGuard, ite_eq_left hi] using hg

/-- Below thirty billion all seven high guards reduce to the supplied base. -/
theorem tunedHigh_eq_base {L B : ℝ} (hL : L < 30000000000) : tunedHighMin L B = B := by
  have hi (i : Fin 7) : ¬(Analysis.triangularTunedProfile i).T ≤ L := by
    linarith only [(Analysis.triangularTunedProfile i).entry, hL]
  simp only [tunedHighMin, tunedHighGuard, ite_eq_right (hi _), min_self]

end PseudoPrime.PrimeTestBounds.MillerRabin
