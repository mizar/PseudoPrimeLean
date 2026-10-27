/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedEnvelopeStrict
/-! # Exact selections of the improved candidate minimum -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A real C below the compatible envelope and every valid candidate is below the
improved envelope. Split each guard separately and combine the minimum inequalities.
This supplies the lower half of exact interval-selection equalities. -/
theorem improved_lower_of_candidates {n : ℕ} {C : ℝ}
    (hB : C ≤ selectedWitnessEnvelope n)
    (hs : n < 3000 → C ≤ smallIntervalBound n)
    (h61 : Real.log n ≤ 2877 / 250 → C ≤ 61)
    (h67 : Real.log n ≤ 47 / 4 → C ≤ 67)
    (hfour : 45 / 4 ≤ Real.log n → C ≤ LLS.PaperStatements.endpointFourStepCutoff (Real.log n))
    (hgamma : 100 ≤ Real.log n → C ≤ gammaSharpBound (Real.log n))
    (hgauss : 63 ≤ Real.log n → C ≤ Analysis.gaussianFloorSelected (Real.log n))
    (htri : 2000000000000 ≤ Real.log n → C ≤
      (282924 / 1000000 : ℝ) * Real.log n ^ 2) : C ≤ improvedWitnessEnvelope n := by
  have cond {P : Prop} [Decidable P] {v : ℝ} (h : P → C ≤ v) :
      C ≤ if P then v else selectedWitnessEnvelope n := by
    by_cases hp : P
    · rw [ite_eq_left hp]
      exact h hp
    · rw [ite_eq_right hp]
      exact hB
  exact le_min hB (le_min (cond hs) (le_min (cond h61) (le_min (cond h67)
    (le_min (cond hfour) (le_min (cond hgamma) (le_min (cond hgauss) (cond htri)))))))

/-- For n>1 and log n>=2 trillion, the compatible envelope is at least the
coefficient-0.282924 candidate. Both its refined and coefficient branches satisfy this bound. -/
theorem old_high_ge_triangular {n : ℕ} (hn : 1 < n) (hL : 2000000000000 ≤ Real.log n) :
    (282924 / 1000000 : ℝ) * Real.log n ^ 2 ≤ selectedWitnessEnvelope n := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have h11 : ¬Real.log n < 23 / 2 := by linarith only [hL]
  have h120 : ¬Real.log n < 120 := by linarith only [hL]
  have h240 : ¬Real.log n ≤ 240 := by linarith only [hL]
  have hS : ¬Real.log n ≤ gammaFixedSwitch := by
    linarith only [hL, gammaFixedSwitch_bounds.2]
  simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h61, ite_eq_right h11, ite_eq_right h120, ite_eq_right hS,
    ite_eq_right h240, gaussianMRWitnessEnvelope]
  by_cases h : 10 ^ 9565217391305 ≤ n
  · rw [ite_eq_left h, gaussianMRLargeEnvelope_eq (by linarith only [hL])]
  · have h300 : (300 : ℝ) ≤ Real.log n := by linarith only [hL]
    rw [ite_eq_right h, ite_eq_left h300, gaussianMRRefinedEnvelope_eq h300]
    have hlocal := Analysis.gaussianMRRefined_local h300
    nlinarith only [hlocal, sq_nonneg (Real.log n)]

/-- For n>1 and log n>=2 trillion, the improved minimum equals 0.282924 log(n)
squared. Quadratic lower bounds remove every other active candidate. -/
theorem improved_eq_triangular {n : ℕ} (hn : 1 < n) (hL : 2000000000000 ≤ Real.log n) :
    improvedWitnessEnvelope n = (282924 / 1000000 : ℝ) * Real.log n ^ 2 := by
  apply le_antisymm (improved_le_triangular hL)
  apply improved_lower_of_candidates (old_high_ge_triangular hn hL)
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    have hl := LLS.PaperStatements.fourStep_quadratic_lower
      (by linarith only [hL] : (240 : ℝ) ≤ Real.log n)
    nlinarith only [hl, sq_nonneg (Real.log n)]
  · intro _
    have hl := sharp_quadratic_lower (by linarith only [hL] : (100 : ℝ) ≤ Real.log n)
    nlinarith only [hl, sq_nonneg (Real.log n)]
  · intro _
    have hl := Analysis.gaussianFloorSelected_lower (by linarith only [hL])
    nlinarith only [hl, sq_nonneg (Real.log n)]
  · intro _
    exact le_refl _
/-- For n>1 and 240<log n<2 trillion, the improved minimum equals the selected
clipped Gaussian envelope. Global comparisons remove C4 and G1, and the decimal threshold
excludes the compatible coefficient branch. -/
theorem improved_eq_gaussian {n : ℕ} (hn : 1 < n) (hL : 240 < Real.log n)
    (hU : Real.log n < 2000000000000) :
    improvedWitnessEnvelope n = Analysis.gaussianFloorSelected (Real.log n) := by
  have hNold : n < 10 ^ 9565217391305 := by
    by_contra h
    have hl := log_ge_triangular_large_index_of_decimal (le_of_not_gt h)
    linarith only [hl, hU]
  apply le_antisymm (improved_le_gaussian (by linarith only [hL]))
  apply improved_lower_of_candidates (gaussianSelected_lt_old hn hL hNold).le
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    exact (gaussianSelected_lt_fourStep hL.le).le
  · intro _
    exact (gaussianSelected_lt_sharp hL.le).le
  · intro _
    exact le_refl _
  · intro h
    exfalso
    linarith only [hU, h]

/-- For n>1 and 11.5<=log n<120, the compatible envelope equals its two-step
cutoff. Simplify the integer and logarithmic guards for later dominance proofs. -/
theorem old_eq_twoStep_low {n : ℕ} (hn : 1 < n)
    (hL : 23 / 2 ≤ Real.log n) (hU : Real.log n < 120) :
    selectedWitnessEnvelope n =
      LLS.PaperStatements.fullEndpointEvenTwoStepCutoff (Real.log n) := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h61, ite_eq_right (not_lt.mpr hL), ite_eq_left hU]

/-- For 11.5<=L<=120, C4<35000. Combine C4<=C2 with the certified two-step
comparison. This removes the clipped Gaussian floor from lower intervals. -/
theorem fourStep_lt_fixed_low {L : ℝ} (hL : 23 / 2 ≤ L) (hU : L ≤ 120) :
    LLS.PaperStatements.endpointFourStepCutoff L < 35000 := by
  exact (LLS.PaperStatements.endpoint_fourStep_le_two
    (by linarith only [hL])).trans_lt (twoStep_lt_fixed hL hU)

/-- For n>1 and 11.75<log n<100, the improved minimum equals C4. The two-step
comparison and fixed Gaussian floor dominate C4; all other candidates are inactive. -/
theorem improved_eq_fourStep {n : ℕ} (hn : 1 < n) (hL : 47 / 4 < Real.log n)
    (hU : Real.log n < 100) :
    improvedWitnessEnvelope n = LLS.PaperStatements.endpointFourStepCutoff (Real.log n) := by
  have hbase : (45 / 4 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply le_antisymm (improved_le_fourStep hbase)
  apply improved_lower_of_candidates
  · rw [old_eq_twoStep_low hn (by linarith only [hL]) (by linarith only [hU])]
    exact LLS.PaperStatements.endpoint_fourStep_le_two hbase
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    exact le_refl _
  · intro h
    exfalso
    linarith only [hU, h]
  · intro _
    rw [Analysis.gaussianFloorSelected_eq_fixed
      (by linarith only [hU, Analysis.gaussianFloor_switch35_bounds.1])]
    exact (fourStep_lt_fixed_low (by linarith only [hL]) (by linarith only [hU])).le
  · intro h
    exfalso
    linarith only [hU, h]

/-- For n>1 and 100<=log n<112, the improved envelope equals min(C4,G1).
Remove every other candidate without assuming an uncertified numerical crossing. -/
theorem improved_eq_middle_min {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n < 112) :
    improvedWitnessEnvelope n = min (LLS.PaperStatements.endpointFourStepCutoff (Real.log n))
      (gammaSharpBound (Real.log n)) := by
  have hf := improved_le_fourStep (by linarith only [hL] : (45 / 4 : ℝ) ≤ Real.log n)
  have hg := improved_le_sharp hL
  apply le_antisymm (le_min hf hg)
  apply improved_lower_of_candidates
  · rw [old_eq_twoStep_low hn (by linarith only [hL]) (by linarith only [hU])]
    exact (min_le_left _ _).trans (LLS.PaperStatements.endpoint_fourStep_le_two
      (by linarith only [hL]))
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    exact min_le_left _ _
  · intro _
    exact min_le_right _ _
  · intro _
    rw [Analysis.gaussianFloorSelected_eq_fixed
      (by linarith only [hU, Analysis.gaussianFloor_switch35_bounds.1])]
    exact (min_le_left _ _).trans (fourStep_lt_fixed_low
      (by linarith only [hL]) (by linarith only [hU])).le
  · intro h
    exfalso
    linarith only [hU, h]

/-- For 112<=L<=240, G1<=C4. Combine the two low correction-cap bands and
the five middle bands. The comparison covers every real point of the interval. -/
theorem sharp_le_fourStep_full {L : ℝ} (hL : 112 ≤ L) (hU : L ≤ 240) :
    gammaSharpBound L ≤ LLS.PaperStatements.endpointFourStepCutoff L := by
  by_cases h : L ≤ 120
  · exact (gammaSharp_lt_fourStep hL h).le
  · exact (sharp_lt_fourStep_middle (le_of_not_ge h) hU).le

/-- For n>1 and 112<=log n<=S1, G1 is at most the compatible envelope.
Compare its two-step, Gamma and fixed branches on their exact guarded intervals. -/
theorem old_ge_sharp {n : ℕ} (hn : 1 < n) (hL : 112 ≤ Real.log n)
    (hS : Real.log n ≤ gammaSharpFixedSwitch) :
    gammaSharpBound (Real.log n) ≤ selectedWitnessEnvelope n := by
  have h240 : Real.log n ≤ 240 := by linarith only [hS, gammaSharpFixedSwitch_bounds.2]
  by_cases h120 : Real.log n < 120
  · rw [old_eq_twoStep_low hn (by linarith only [hL]) h120]
    exact (sharp_le_fourStep_full hL h240).trans
      (LLS.PaperStatements.endpoint_fourStep_le_two (by linarith only [hL]))
  · have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    have h3 : ¬n < 3000 := not_lt.mpr hN
    have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
    have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
    have h11 : ¬Real.log n < 23 / 2 := by linarith only [hL]
    simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3,
      ite_eq_right h61, ite_eq_right h11, ite_eq_right h120]
    by_cases h : Real.log n ≤ gammaFixedSwitch
    · rw [ite_eq_left h]
      exact (gammaSharp_lt_refined (le_of_not_gt h120) h240).le
    · rw [ite_eq_right h, ite_eq_left h240]
      exact gammaSharp_le_fixed (by linarith only [hL]) hS

/-- For n>1 and 112<=log n<=S1, the improved minimum equals G1. The
continuous C4 comparison and exact fixed switch remove all other candidates. -/
theorem improved_eq_sharp {n : ℕ} (hn : 1 < n) (hL : 112 ≤ Real.log n)
    (hS : Real.log n ≤ gammaSharpFixedSwitch) :
    improvedWitnessEnvelope n = gammaSharpBound (Real.log n) := by
  have h240 : Real.log n ≤ 240 := by linarith only [hS, gammaSharpFixedSwitch_bounds.2]
  apply le_antisymm (improved_le_sharp (by linarith only [hL]))
  apply improved_lower_of_candidates (old_ge_sharp hn hL hS)
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    exact sharp_le_fourStep_full hL h240
  · intro _
    exact le_refl _
  · intro _
    rw [Analysis.gaussianFloorSelected_eq_fixed
      (h240.trans Analysis.gaussianFloor_switch35_bounds.1.le)]
    exact gammaSharp_le_fixed (by linarith only [hL]) hS
  · intro h
    exfalso
    linarith only [h240, h]

/-- For n>1 and S1<=log n<=240, the improved minimum equals 35000.
Both G1 and C4 are above the floor, and the Gaussian envelope attains it. -/
theorem improved_eq_fixed35000 {n : ℕ} (hn : 1 < n)
    (hS : gammaSharpFixedSwitch ≤ Real.log n) (hU : Real.log n ≤ 240) :
    improvedWitnessEnvelope n = 35000 := by
  have hL : (120 : ℝ) ≤ Real.log n := by
    linarith only [hS, gammaSharpFixedSwitch_bounds.1]
  have hf : Analysis.gaussianFloorSelected (Real.log n) = 35000 :=
    Analysis.gaussianFloorSelected_eq_fixed
      (hU.trans Analysis.gaussianFloor_switch35_bounds.1.le)
  have hg : (35000 : ℝ) ≤ gammaSharpBound (Real.log n) :=
    fixed_le_gammaSharp (by linarith only [hL]) hS
  apply le_antisymm (hf ▸ improved_le_gaussian (by linarith only [hL]))
  apply improved_lower_of_candidates
  · rw [← midscale_eq_selected hn, midscale_eq_fixed hn
      (by linarith only [hS, gammaSharpFixedSwitch_bounds.1, gammaFixedSwitch_bounds.2]) hU]
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    exact hg.trans (sharp_le_fourStep_full (by linarith only [hL]) hU)
  · intro _
    exact hg
  · intro _
    exact hf.ge
  · intro h
    exfalso
    linarith only [hU, h]

/-- For L>=45/4, C4>64. The fourth radius strictly exceeds the clipped third
radius, which is at least eight. This removes C4 from the fixed-61 interval. -/
theorem fourStep_gt64 {L : ℝ} (hL : 45 / 4 ≤ L) :
    (64 : ℝ) < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : (8 : ℝ) ≤ LLS.PaperStatements.endpointThirdRadius L := le_max_left _ _
  have hd := (LLS.PaperStatements.endpoint_fourth_bounds hL).1
  dsimp only [LLS.PaperStatements.endpointFourStepCutoff]
  nlinarith only [hc, hd, sq_nonneg (LLS.PaperStatements.endpointFourthRadius L - 8)]

/-- For n>1 and 11.508<log n<=11.75, the improved minimum equals 67.
The continuous fourth-radius comparison dominates 67 and the 61 candidate is inactive. -/
theorem improved_eq_fixed67 {n : ℕ} (hn : 1 < n) (hL : 2877 / 250 < Real.log n)
    (hU : Real.log n ≤ 47 / 4) : improvedWitnessEnvelope n = 67 := by
  have hf := LLS.PaperStatements.fourStep_gt67 hL.le hU
  apply le_antisymm (improved_le_fixed67 hU)
  apply improved_lower_of_candidates
  · rw [old_eq_twoStep_low hn (by linarith only [hL]) (by linarith only [hU])]
    exact hf.le.trans (LLS.PaperStatements.endpoint_fourStep_le_two
      (by linarith only [hL]))
  · intro h
    have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
    exact False.elim (not_lt.mpr hN h)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro _
    exact le_refl _
  · intro _
    exact hf.le
  · intro h
    exfalso
    linarith only [hU, h]
  · intro h
    exfalso
    linarith only [hU, h]
  · intro h
    exfalso
    linarith only [hU, h]

/-- For n>=3000 and log n<=11.508, the compatible envelope is at least 61.
Check its fixed, shifted-quadratic and two-step branches using exact rational bounds. -/
theorem old_low_ge61 {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n ≤ 2877 / 250) :
    (61 : ℝ) ≤ selectedWitnessEnvelope n := by
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3]
  by_cases h61 : Real.log n ≤ 286 / 25
  · rw [ite_eq_left h61]
  · rw [ite_eq_right h61]
    by_cases h11 : Real.log n < 23 / 2
    · rw [ite_eq_left h11]
      have hl : (286 / 25 : ℝ) ≤ Real.log n := le_of_not_ge h61
      nlinarith only [hl, sq_nonneg (Real.log n - 286 / 25)]
    · have h120 : Real.log n < 120 := by linarith only [hU]
      rw [ite_eq_right h11, ite_eq_left h120]
      have hb : (45 / 4 : ℝ) ≤ Real.log n := by linarith only [le_of_not_gt h11]
      exact (by norm_num only : (61 : ℝ) ≤ 64).trans ((fourStep_gt64 hb).le.trans
        (LLS.PaperStatements.endpoint_fourStep_le_two hb))

/-- For n>=3000 and log n<=11.508, the improved minimum equals 61.
Its pointwise gap supplies 61; all active alternative candidates are at least 61. -/
theorem improved_eq_fixed61 {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n ≤ 2877 / 250) :
    improvedWitnessEnvelope n = 61 := by
  apply le_antisymm (improved_le_fixed61 hU)
  apply improved_lower_of_candidates (old_low_ge61 hN hU)
  · intro h
    exact False.elim (not_lt.mpr hN h)
  · intro _
    exact le_refl _
  · intro _
    norm_num only
  · intro h
    exact (by norm_num only : (61 : ℝ) ≤ 64).trans (fourStep_gt64 h).le
  · intro h
    exfalso
    linarith only [hU, h]
  · intro h
    exfalso
    linarith only [hU, h]
  · intro h
    exfalso
    linarith only [hU, h]

/-- For 1<n<3000, the improved minimum equals two below 2047 and three
throughout 2047<=n<3000. A logarithmic cap excludes all nonconstant analytic candidates. -/
theorem improved_eq_small {n : ℕ} (hn : 1 < n) (hN : n < 3000) :
    improvedWitnessEnvelope n = smallIntervalBound n := by
  have hcast : (n : ℝ) ≤ 46000 := by
    exact_mod_cast (hN.le.trans (by norm_num only : 3000 ≤ 46000))
  have hL : Real.log n < 11 :=
    (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hcast).trans_lt
      Analysis.log_46000_lt_eleven
  have hsmall : smallIntervalBound n ≤ (3 : ℝ) := by
    by_cases h : n < 2047
    · simp only [smallIntervalBound, ite_eq_left h]
      norm_num only
    · simp only [smallIntervalBound, ite_eq_right h, le_refl]
  apply le_antisymm (improved_le_small hN)
  apply improved_lower_of_candidates
  · by_cases h2 : n < 2047
    · simp only [selectedWitnessEnvelope, smallIntervalBound, ite_eq_left h2, le_refl]
    · simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_left hN]
      exact hsmall
  · intro _
    exact le_refl _
  · intro _
    exact hsmall.trans (by norm_num only)
  · intro _
    exact hsmall.trans (by norm_num only)
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]
  · intro h
    exfalso
    linarith only [hL, h]

/-- The explicit interval selection of the improved MR witness envelope.
It retains min(C4,G1) only on 100<=log n<112, uses exact Gamma and Gaussian switches,
and starts the coefficient branch at log n>=2 trillion. The equality theorem certifies it. -/
noncomputable def improvedSelectedEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  if n < 3000 then smallIntervalBound n
  else if L ≤ 2877 / 250 then 61
  else if L ≤ 47 / 4 then 67
  else if L < 100 then LLS.PaperStatements.endpointFourStepCutoff L
  else if L < 112 then min (LLS.PaperStatements.endpointFourStepCutoff L) (gammaSharpBound L)
  else if L ≤ gammaSharpFixedSwitch then gammaSharpBound L
  else if L ≤ 240 then 35000
  else if L < 2000000000000 then Analysis.gaussianFloorSelected L
  else (282924 / 1000000 : ℝ) * L ^ 2

/-- For every n>1, the guarded candidate minimum equals its explicit interval
selection. Apply the proved branch equalities at each exact guard, including every endpoint. -/
theorem improved_eq_selected {n : ℕ} (hn : 1 < n) :
    improvedWitnessEnvelope n = improvedSelectedEnvelope n := by
  dsimp only [improvedSelectedEnvelope]
  by_cases hs : n < 3000
  · rw [ite_eq_left hs]
    exact improved_eq_small hn hs
  rw [ite_eq_right hs]
  by_cases h61 : Real.log n ≤ 2877 / 250
  · rw [ite_eq_left h61]
    exact improved_eq_fixed61 (le_of_not_gt hs) h61
  rw [ite_eq_right h61]
  by_cases h67 : Real.log n ≤ 47 / 4
  · rw [ite_eq_left h67]
    exact improved_eq_fixed67 hn (lt_of_not_ge h61) h67
  rw [ite_eq_right h67]
  by_cases h100 : Real.log n < 100
  · rw [ite_eq_left h100]
    exact improved_eq_fourStep hn (lt_of_not_ge h67) h100
  rw [ite_eq_right h100]
  by_cases h112 : Real.log n < 112
  · rw [ite_eq_left h112]
    exact improved_eq_middle_min hn (le_of_not_gt h100) h112
  rw [ite_eq_right h112]
  by_cases hS : Real.log n ≤ gammaSharpFixedSwitch
  · rw [ite_eq_left hS]
    exact improved_eq_sharp hn (le_of_not_gt h112) hS
  rw [ite_eq_right hS]
  by_cases h240 : Real.log n ≤ 240
  · rw [ite_eq_left h240]
    exact improved_eq_fixed35000 hn (le_of_not_ge hS) h240
  rw [ite_eq_right h240]
  by_cases hT : Real.log n < 2000000000000
  · rw [ite_eq_left hT]
    exact improved_eq_gaussian hn (lt_of_not_ge h240) hT
  rw [ite_eq_right hT]
  exact improved_eq_triangular hn (le_of_not_gt hT)

/-- Under GRH, every odd composite n>1 has an actual prime rejecting strong MR
within the explicit improved selection. Transfer through the exact envelope equality. -/
theorem exists_prime_improvedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ improvedSelectedEnvelope n ∧
      ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← improved_eq_selected hn]
  exact exists_prime_improvedWitness hn ho hc hGRH

/-- Under GRH, every odd composite n>1 has a least prime rejecting strong MR
within the explicit improved selection. The exact selection equality preserves minimality. -/
theorem exists_least_improvedSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
      (p : ℝ) ≤ improvedSelectedEnvelope n ∧
      ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← improved_eq_selected hn]
  exact exists_least_improvedWitness hn ho hc hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
