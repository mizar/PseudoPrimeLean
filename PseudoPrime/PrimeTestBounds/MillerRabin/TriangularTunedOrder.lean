/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpNormalForm
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededCurrentOrder

/-! # Exact current high selection and tuned strict improvement -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Each tuned certificate preserves its entrance and strictly lowers its old coefficient. -/
theorem triangularTuned_stage_data (i : Fin 7) :
    (Analysis.triangularTunedProfile i).T = (Analysis.triangularProfile i.castSucc).T ∧
      (Analysis.triangularTunedProfile i).C < (Analysis.triangularProfile i.castSucc).C ∧
      (Analysis.triangularProfile i.castSucc).C ≤ (7 / 15 : ℝ) := by
  fin_cases i <;> dsimp only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;>
    norm_num only [Analysis.triangularProfile, Analysis.triangularTunedProfile,
      Analysis.triangularP0466, Analysis.triangularP042, Analysis.triangularP0333,
      Analysis.triangularP030, Analysis.triangularP029, Analysis.triangularP0284,
      Analysis.triangularP02829, Analysis.triangularP02823622, Analysis.triangularP04603,
      Analysis.triangularP04145, Analysis.triangularP03315, Analysis.triangularP02992,
      Analysis.triangularP02891, Analysis.triangularP028399, Analysis.triangularP028289,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.reduceAdd, and_self]
  all_goals
    change (1480000000000 : ℝ) = 1480000000000 ∧ (28289 / 100000 : ℝ) < 2829 / 10000 ∧ True
    norm_num only [and_self]

/-- Before the next entrance the currently active coefficient is the smallest valid one. -/
theorem triangularStage_best (i : Fin 7) {L : ℝ} (hU : L < (Analysis.triangularProfile i.succ).T)
    (j : Fin 8) (hj : (Analysis.triangularProfile j).T ≤ L) :
    (Analysis.triangularProfile i.castSucc).C ≤ (Analysis.triangularProfile j).C := by
  fin_cases i <;> fin_cases j <;>
    dsimp only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;>
    norm_num only [Analysis.triangularProfile, Analysis.triangularTunedProfile,
      Analysis.triangularP0466, Analysis.triangularP042, Analysis.triangularP0333,
      Analysis.triangularP030, Analysis.triangularP029, Analysis.triangularP0284,
      Analysis.triangularP02829, Analysis.triangularP02823622, Analysis.triangularP04603,
      Analysis.triangularP04145, Analysis.triangularP03315, Analysis.triangularP02992,
      Analysis.triangularP02891, Analysis.triangularP028399, Analysis.triangularP028289,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.reduceAdd] at hU hj ⊢ <;>
    first
    | linarith only [hU, hj]
    | (change (1820000000000 : ℝ) ≤ L at hj; linarith only [hU, hj])

/-- After scale 1.1 trillion, the active pre-final coefficient is at most 0.284. -/
theorem triangularStage_after11 (i : Fin 7) {L : ℝ} (hU : L < (Analysis.triangularProfile i.succ).T)
    (hL : 1100000000000 ≤ L) : (Analysis.triangularProfile i.castSucc).C ≤ (71 / 250 : ℝ) := by
  fin_cases i <;> dsimp only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;>
    norm_num only [Analysis.triangularProfile, Analysis.triangularTunedProfile,
      Analysis.triangularP0466, Analysis.triangularP042, Analysis.triangularP0333,
      Analysis.triangularP030, Analysis.triangularP029, Analysis.triangularP0284,
      Analysis.triangularP02829, Analysis.triangularP02823622, Analysis.triangularP04603,
      Analysis.triangularP04145, Analysis.triangularP03315, Analysis.triangularP02992,
      Analysis.triangularP02891, Analysis.triangularP028399, Analysis.triangularP028289,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.reduceAdd] at hU ⊢ <;>
    linarith only [hU, hL]

/-- After scale 1.5 trillion, the active pre-final coefficient is at most 0.282924. -/
theorem triangularStage_after15 (i : Fin 7) {L : ℝ} (hU : L < (Analysis.triangularProfile i.succ).T)
    (hL : 1500000000000 ≤ L) :
    (Analysis.triangularProfile i.castSucc).C ≤ (282924 / 1000000 : ℝ) := by
  fin_cases i <;> dsimp only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;>
    norm_num only [Analysis.triangularProfile, Analysis.triangularTunedProfile,
      Analysis.triangularP0466, Analysis.triangularP042, Analysis.triangularP0333,
      Analysis.triangularP030, Analysis.triangularP029, Analysis.triangularP0284,
      Analysis.triangularP02829, Analysis.triangularP02823622, Analysis.triangularP04603,
      Analysis.triangularP04145, Analysis.triangularP03315, Analysis.triangularP02992,
      Analysis.triangularP02891, Analysis.triangularP028399, Analysis.triangularP028289,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.reduceAdd] at hU ⊢ <;>
    linarith only [hU, hL]

/-- The next entrance of each of the first seven stages is no later than 1.82 trillion. -/
theorem triangularStage_next_le (i : Fin 7) :
    (Analysis.triangularProfile i.succ).T ≤ (1820000000000 : ℝ) := by
  fin_cases i <;> dsimp only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;>
    norm_num only [Analysis.triangularProfile, Analysis.triangularTunedProfile,
      Analysis.triangularP0466, Analysis.triangularP042, Analysis.triangularP0333,
      Analysis.triangularP030, Analysis.triangularP029, Analysis.triangularP0284,
      Analysis.triangularP02829, Analysis.triangularP02823622, Analysis.triangularP04603,
      Analysis.triangularP04145, Analysis.triangularP03315, Analysis.triangularP02992,
      Analysis.triangularP02891, Analysis.triangularP028399, Analysis.triangularP028289,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ, Nat.reduceAdd]
  all_goals
    change (1820000000000 : ℝ) ≤ 1820000000000
    exact le_rfl

/-- On [1.1,1.5) trillion the current refined envelope is at least 0.284 L².
Every active analytic candidate exceeds 15L²/32 and the old high candidate is equal. -/
theorem refined_early_quadratic_lower {n : ℕ} (hn : 1 < n) (hL : (1100000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1500000000000) :
    (71 / 250 : ℝ) * Real.log n ^ 2 ≤ refinedSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h240 : (240 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hcoef : (71 / 250 : ℝ) * Real.log n ^ 2 ≤ (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  have hS := hcoef.trans (currentSeeded_quadratic_lower h63).le
  rw [← refined_eq_selected hn]
  apply refined_lower_of_candidates
  · rw [lowPrimeTight_eq_next_of_log (by linarith only [hL]), next_eq_seeded hn h240 hU]
    exact hcoef.trans (Analysis.gaussianSeededSelected_lower h63).le
  · intro _
    exact hcoef.trans (Analysis.gaussianRecovered_bound_lower h63).le
  · intro _
    exact hS.trans (currentSeeded_le_gamma h240)
  · intro _
    exact hS
  · intro _
    exact le_rfl
  · intro hh
    exfalso
    linarith only [hU, hh]

/-- Every current Gaussian profile is strictly above the common quadratic lower bound. -/
theorem gaussianLowFamily_quadratic_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < Analysis.gaussianLowFamily L := by
  have hf (f : Analysis.GaussianLowProfile) : (15 / 32 : ℝ) * L ^ 2 < f.bound L := by
    have hr := f.radius_linear hL
    have hp : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
    have hs := (sq_lt_sq₀ hp (hp.trans hr.le)).mpr hr
    change _ < (6 / 5 : ℝ) * f.radius L ^ 2
    nlinarith only [hs]
  exact lt_min (hf .low) (lt_min (hf .middle) (hf .upper))

/-- The current seeded minimum has the same strict quadratic lower bound. -/
theorem seededSharp_quadratic_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < Analysis.gaussianSeededSharp L := by
  rw [Analysis.gaussianSeededSharp_eq_min hL]
  exact
    lt_min (Analysis.gaussianSeededSharp_bound_lower hL)
      (Analysis.gaussianSeededSharp_bound_lower hL)

/-- Throughout a current high stage, the refined base is no smaller than its
active triangular cutoff. The 1.1--1.5 trillion subrange retains the stronger 0.284 floor. -/
theorem triangularStage_le_refined (i : Fin 7) {n : ℕ} (hn : 1 < n)
    (hL : (Analysis.triangularProfile i.castSucc).T ≤ Real.log n)
    (hU : Real.log n < (Analysis.triangularProfile i.succ).T) :
    (Analysis.triangularProfile i.castSucc).C * Real.log n ^ 2 ≤ refinedSelectedEnvelope n := by
  have hentry := (Analysis.triangularProfile i.castSucc).entry.trans hL
  have hupper := hU.trans_le (triangularStage_next_le i)
  by_cases h11 : Real.log n < 1100000000000
  · rw [refinedSelected_eq_currentSeeded hn (by linarith only [hentry]) h11]
    have hc := (triangularTuned_stage_data i).2.2
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log n))
    have hs := currentSeeded_quadratic_lower (by linarith only [hentry] : (63 : ℝ) ≤ Real.log n)
    nlinarith only [hm, hs, sq_nonneg (Real.log n)]
  · by_cases h15 : Real.log n < 1500000000000
    · exact
        (mul_le_mul_of_nonneg_right (triangularStage_after11 i hU (le_of_not_gt h11))
              (sq_nonneg _)).trans
          (refined_early_quadratic_lower hn (le_of_not_gt h11) h15)
    · exact
        (mul_le_mul_of_nonneg_right (triangularStage_after15 i hU (le_of_not_gt h15))
              (sq_nonneg _)).trans
          (refined_mid_quadratic_lower hn (le_of_not_gt h11) (by linarith only [hupper]))

/-- In each pre-final high stage, the public current sharp selection is
exactly the active current triangular cutoff. All competing candidates are bounded below. -/
theorem sharpSelected_eq_triangularStage (i : Fin 7) {n : ℕ} (hn : 1 < n)
    (hL : (Analysis.triangularProfile i.castSucc).T ≤ Real.log n)
    (hU : Real.log n < (Analysis.triangularProfile i.succ).T) :
    sharpSelectedEnvelope n = (Analysis.triangularProfile i.castSucc).C * Real.log n ^ 2 := by
  have hentry := (Analysis.triangularProfile i.castSucc).entry.trans hL
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hentry]
  have hB := triangularStage_le_refined i hn hL hU
  rw [← lowFiniteSelected_eq_refined hn (by linarith only [hentry])] at hB
  have hcoef :=
    mul_le_mul_of_nonneg_right (triangularTuned_stage_data i).2.2 (sq_nonneg (Real.log n))
  have hG :
    (Analysis.triangularProfile i.castSucc).C * Real.log n ^ 2 ≤
      Analysis.gaussianLowFamily (Real.log n) := by
    have hs := gaussianLowFamily_quadratic_lower h63
    nlinarith only [hcoef, hs, sq_nonneg (Real.log n)]
  have hS :
    (Analysis.triangularProfile i.castSucc).C * Real.log n ^ 2 ≤
      Analysis.gaussianSeededSharp (Real.log n) := by
    have hs := seededSharp_quadratic_lower h63
    nlinarith only [hcoef, hs, sq_nonneg (Real.log n)]
  rw [sharpSelectedEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 h63)), sharpGuardSelected,
    ite_eq_right (not_lt.mpr h63), sharpHigh_eq_active i.castSucc hL (triangularStage_best i hU),
    min_eq_right hB, min_eq_right hS, min_eq_right hG, min_eq_right hB]

/-- Each tuned profile strictly improves the public current sharp value on its
full original stage, since its entrance is unchanged and its coefficient is smaller. -/
theorem triangularTuned_strict_stage (i : Fin 7) {n : ℕ} (hn : 1 < n)
    (hL : (Analysis.triangularProfile i.castSucc).T ≤ Real.log n)
    (hU : Real.log n < (Analysis.triangularProfile i.succ).T) :
    (Analysis.triangularTunedProfile i).C * Real.log n ^ 2 < sharpSelectedEnvelope n := by
  rw [sharpSelected_eq_triangularStage i hn hL hU]
  have hp :=
    sq_pos_of_pos
      (show (0 : ℝ) < Real.log n from
        lt_of_lt_of_le (by norm_num only) ((Analysis.triangularProfile i.castSucc).entry.trans hL))
  exact mul_lt_mul_of_pos_right (triangularTuned_stage_data i).2.1 hp

/-- Every scale in the union of the first seven current high stages has one active stage.
Successive exact rational entrances cover the entire half-open interval. -/
theorem triangularStage_exists {L : ℝ} (hL : (30000000000 : ℝ) ≤ L) (hU : L < 1820000000000) :
    ∃ i : Fin 7,
      (Analysis.triangularProfile i.castSucc).T ≤ L ∧
        L < (Analysis.triangularProfile i.succ).T := by
  by_cases h0 : L < 40000000000
  · exact ⟨0, hL, h0⟩
  by_cases h1 : L < 100000000000
  · exact ⟨1, le_of_not_gt h0, h1⟩
  by_cases h2 : L < 250000000000
  · exact ⟨2, le_of_not_gt h1, h2⟩
  by_cases h3 : L < 500000000000
  · exact ⟨3, le_of_not_gt h2, h3⟩
  by_cases h4 : L < 1080000000000
  · exact ⟨4, le_of_not_gt h3, h4⟩
  by_cases h5 : L < 1480000000000
  · exact ⟨5, le_of_not_gt h4, h5⟩
  exact ⟨6, le_of_not_gt h5, hU⟩

/-- On [30 billion,1.82 trillion), an active tuned certificate strictly improves
the current public sharp selection. The final current eighth stage is unchanged. -/
theorem triangularTuned_strict_high {n : ℕ} (hn : 1 < n) (hL : (30000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1820000000000) :
    ∃ i : Fin 7,
      (Analysis.triangularTunedProfile i).T ≤ Real.log n ∧
        (Analysis.triangularTunedProfile i).C * Real.log n ^ 2 < sharpSelectedEnvelope n := by
  obtain ⟨i, hi, hu⟩ := triangularStage_exists hL hU
  refine ⟨i, ?_, triangularTuned_strict_stage i hn hi hu⟩
  rw [(triangularTuned_stage_data i).1]
  exact hi

end PseudoPrime.PrimeTestBounds.MillerRabin
