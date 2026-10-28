/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.NextWitnessEnvelope
public import PseudoPrime.LLS.EndpointPointwiseGrowth
public import PseudoPrime.Analysis.GaussianSeededGrowth

/-! # Exact interval selection for the next all-input envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Transfer a common lower bound through every guarded next candidate. -/
theorem next_lower_of_candidates {n : ℕ} {C : ℝ} (hB : C ≤ lowPrimeEnvelope n)
    (hP : C ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n))
    (hA : 63 ≤ Real.log n → C ≤ Analysis.gaussian1000Bound (Real.log n))
    (hG : 100 ≤ Real.log n → C ≤ gammaReflectedBound (Real.log n))
    (hS : 63 ≤ Real.log n → C ≤ Analysis.gaussianSeededSelected (Real.log n))
    (h61 : Real.log n ≤ 11509 / 1000 → C ≤ 61) (h67 : Real.log n ≤ 1179 / 100 → C ≤ 67)
    (h71 : Real.log n ≤ 1193 / 100 → C ≤ 71) (h73 : Real.log n ≤ 12337 / 1000 → C ≤ 73)
    (hE : 1500000000000 ≤ Real.log n → C ≤ (282924 / 1000000) * Real.log n ^ 2)
    (hT : 2000000000000 ≤ Real.log n → C ≤ (2827 / 10000) * Real.log n ^ 2) :
    C ≤ nextWitnessEnvelope n := by
  classical
  have guard (P : Prop) (X : ℝ) (hx : P → C ≤ X) : C ≤ (if P then X else lowPrimeEnvelope n) := by
    by_cases h : P
    · rw [ite_eq_left h]
      exact hx h
    · rw [ite_eq_right h]
      exact hB
  exact
    le_min hB
      (le_min hP
        (le_min (guard _ _ hA)
          (le_min (guard _ _ hG)
            (le_min (guard _ _ hS)
              (le_min (guard _ _ h61)
                (le_min (guard _ _ h67)
                  (le_min (guard _ _ h71)
                    (le_min (guard _ _ h73) (le_min (guard _ _ hE) (guard _ _ hT))))))))))

/-- Beyond the last low-prime cap, the low-prime envelope is exactly its base. -/
theorem lowPrime_eq_improved_of_log {n : ℕ} (hL : 553 / 50 < Real.log n) :
    lowPrimeEnvelope n = improvedWitnessEnvelope n := by
  have h23 : ¬Real.log n ≤ 401 / 50 := by
    intro h; linarith only [hL, h]
  have h29 : ¬Real.log n ≤ 413 / 50 := by
    intro h; linarith only [hL, h]
  have h31 : ¬Real.log n ≤ 893 / 100 := by
    intro h; linarith only [hL, h]
  have h37 : ¬Real.log n ≤ 933 / 100 := by
    intro h; linarith only [hL, h]
  have h41 : ¬Real.log n ≤ 238 / 25 := by
    intro h; linarith only [hL, h]
  have h43 : ¬Real.log n ≤ 989 / 100 := by
    intro h; linarith only [hL, h]
  have h47 : ¬Real.log n ≤ 521 / 50 := by
    intro h; linarith only [hL, h]
  have h53 : ¬Real.log n ≤ 109 / 10 := by
    intro h; linarith only [hL, h]
  have h59 : ¬Real.log n ≤ 553 / 50 := by
    intro h; linarith only [hL, h]
  simp only [lowPrimeEnvelope, ite_eq_right h23, ite_eq_right h29, ite_eq_right h31,
    ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47, ite_eq_right h53,
    ite_eq_right h59, min_self]

/-- The pointwise inverse cutoff is at least 64 at every real level. -/
theorem pointwiseCutoff_floor (L : ℝ) : (64 : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff L := by
  have hs := (LLS.PaperStatements.pointwiseRadius_spec L).1
  have hr : (0 : ℝ) ≤ LLS.PaperStatements.pointwiseRadius L := by linarith only [hs]
  have hsq := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 8) hr).mpr hs
  norm_num only at hsq
  exact hsq

/-- Through the last low-prime cap, all other next candidates preserve the low envelope. -/
theorem next_eq_low {n : ℕ} (hL : Real.log n ≤ 553 / 50) :
    nextWitnessEnvelope n = lowPrimeEnvelope n := by
  have hb := lowPrime_le_fixed59 hL
  apply le_antisymm (nextWitnessEnvelope_le_low n)
  apply next_lower_of_candidates (le_refl _)
  · exact hb.trans ((by norm_num only : (59 : ℝ) ≤ 64).trans (pointwiseCutoff_floor _))
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro _; exact hb.trans (by norm_num only)
  · intro _; exact hb.trans (by norm_num only)
  · intro _; exact hb.trans (by norm_num only)
  · intro _; exact hb.trans (by norm_num only)
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]

/-- From the last low-prime cap through 11.509, the next envelope equals 61. -/
theorem next_eq_fixed61 {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 553 / 50 < Real.log n)
    (hU : Real.log n ≤ 11509 / 1000) : nextWitnessEnvelope n = 61 := by
  apply le_antisymm (next_le_fixed61 hU)
  have hb : (61 : ℝ) ≤ lowPrimeEnvelope n := by
    rw [lowPrime_eq_improved_of_log hL]
    by_cases h : Real.log n ≤ 2877 / 250
    · rw [improved_eq_fixed61 hN h]
    · rw [improved_eq_fixed67 hn (lt_of_not_ge h) (by linarith only [hU])]
      norm_num only
  apply next_lower_of_candidates hb
  · exact (by norm_num only : (61 : ℝ) ≤ 64).trans (pointwiseCutoff_floor _)
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro _; exact le_rfl
  · intro _; norm_num only
  · intro _; norm_num only
  · intro _; norm_num only
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- The seeded selected cutoff retains its 35000 prefix floor in its certified domain. -/
theorem seededSelected_floor {L : ℝ} (hL : 63 ≤ L) :
    (35000 : ℝ) ≤ Analysis.gaussianSeededSelected L := by
  rw [← Analysis.gaussianSeeded_min_eq_selected hL]
  have h35 := Analysis.gaussianSeeded_cutoff_le false L
  have h50 := Analysis.gaussianSeeded_cutoff_le true L
  norm_num only [Analysis.gaussianSeededCutoff, Bool.false_eq_true, ite_false, ite_true,
    Nat.cast_ofNat] at h35 h50
  exact le_min h35 ((by norm_num only : (35000 : ℝ) ≤ 50000).trans h50)

/-- On the stated short interval only the pointwise cutoff and fixed 67 can be selected. -/
theorem next_eq_min67 {n : ℕ} (hn : 1 < n) (hL : 11509 / 1000 < Real.log n)
    (hU : Real.log n ≤ 1179 / 100) :
    nextWitnessEnvelope n = min 67 (LLS.PaperStatements.pointwiseCutoff (Real.log n)) := by
  let C := min (67 : ℝ) (LLS.PaperStatements.pointwiseCutoff (Real.log n))
  have hb : C ≤ (67 : ℝ) := min_le_left _ _
  have hp : C ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := min_le_right _ _
  apply le_antisymm (le_min (next_le_fixed67 hU) next_le_pointwise)
  have hbase : C ≤ lowPrimeEnvelope n := by
    rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    by_cases h : Real.log n ≤ 47 / 4
    · rw [improved_eq_fixed67 hn (by linarith only [hL]) h]
      exact hb
    · rw [improved_eq_fourStep hn (lt_of_not_ge h) (by linarith only [hU])]
      exact hp.trans (LLS.PaperStatements.pointwiseCutoff_lt_fourStep (by linarith only [hL])).le
  apply next_lower_of_candidates hbase hp
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro _; exact hb
  · intro _; exact hb.trans (by norm_num only)
  · intro _; exact hb.trans (by norm_num only)
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- On the stated short interval only the pointwise cutoff and fixed 71 can be selected. -/
theorem next_eq_min71 {n : ℕ} (hn : 1 < n) (hL : 1179 / 100 < Real.log n)
    (hU : Real.log n ≤ 1193 / 100) :
    nextWitnessEnvelope n = min 71 (LLS.PaperStatements.pointwiseCutoff (Real.log n)) := by
  let C := min (71 : ℝ) (LLS.PaperStatements.pointwiseCutoff (Real.log n))
  have hb : C ≤ (71 : ℝ) := min_le_left _ _
  have hp : C ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := min_le_right _ _
  apply le_antisymm (le_min (next_le_fixed71 hU) next_le_pointwise)
  have hbase : C ≤ lowPrimeEnvelope n := by
    rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    rw [improved_eq_fourStep hn (by linarith only [hL]) (by linarith only [hU])]
    exact hp.trans (LLS.PaperStatements.pointwiseCutoff_lt_fourStep (by linarith only [hL])).le
  apply next_lower_of_candidates hbase hp
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro _; exact hb
  · intro _; exact hb.trans (by norm_num only)
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- On the stated short interval only the pointwise cutoff and fixed 73 can be selected. -/
theorem next_eq_min73 {n : ℕ} (hn : 1 < n) (hL : 1193 / 100 < Real.log n)
    (hU : Real.log n ≤ 12337 / 1000) :
    nextWitnessEnvelope n = min 73 (LLS.PaperStatements.pointwiseCutoff (Real.log n)) := by
  let C := min (73 : ℝ) (LLS.PaperStatements.pointwiseCutoff (Real.log n))
  have hb : C ≤ (73 : ℝ) := min_le_left _ _
  have hp : C ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := min_le_right _ _
  apply le_antisymm (le_min (next_le_fixed73 hU) next_le_pointwise)
  have hbase : C ≤ lowPrimeEnvelope n := by
    rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    rw [improved_eq_fourStep hn (by linarith only [hL]) (by linarith only [hU])]
    exact hp.trans (LLS.PaperStatements.pointwiseCutoff_lt_fourStep (by linarith only [hL])).le
  apply next_lower_of_candidates hbase hp
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro _; exact hb
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- Above the fixed 73 cap and below L=100, the inverse pointwise cutoff is selected. -/
theorem next_eq_pointwise {n : ℕ} (hn : 1 < n) (hL : 12337 / 1000 < Real.log n)
    (hU : Real.log n < 100) :
    nextWitnessEnvelope n = LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
  have hp :=
    LLS.PaperStatements.pointwiseCutoff_lt_square (by linarith only [hL] : (8 : ℝ) < Real.log n)
  have hsq : Real.log n ^ 2 < (10000 : ℝ) := by
    have h0 : 0 ≤ Real.log n := by linarith only [hL]
    nlinarith only [h0, hU]
  apply le_antisymm next_le_pointwise
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL]),
      improved_eq_fourStep hn (by linarith only [hL]) hU]
    exact (LLS.PaperStatements.pointwiseCutoff_lt_fourStep (by linarith only [hL])).le
  · exact le_rfl
  · intro _
    exact
      hp.le.trans
        (hsq.le.trans
          ((by norm_num only : (10000 : ℝ) ≤ 12000).trans (Analysis.gaussian1000_cutoff_floor _)))
  · intro h; exfalso; linarith only [hU, h]
  · intro h
    exact
      hp.le.trans
        (hsq.le.trans ((by norm_num only : (10000 : ℝ) ≤ 35000).trans (seededSelected_floor h)))
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- From L>=132 the reflected cutoff is above (16/25)L^2. -/
theorem reflected_linear_lower {L : ℝ} (hL : 132 ≤ L) :
    (16 / 25 : ℝ) * L ^ 2 < gammaReflectedBound L := by
  have hr := gammaReflectedRoot_lower_affine (by linarith only [hL] : 100 ≤ L)
  have hp : (0 : ℝ) ≤ (67 / 125) * L := by linarith only [hL]
  have hroot : (67 / 125 : ℝ) * L < gammaReflectedRoot L := by linarith only [hr]
  have hsq := (sq_lt_sq₀ hp (gammaReflectedRoot_pos (by linarith only [hL])).le).mpr hroot
  dsimp only [gammaReflectedBound]
  nlinarith only [hsq, sq_nonneg L]

/-- Through the triangular entrance, the selected seeded cutoff is no larger than
its previous base on the whole range beginning at L=240. -/
theorem seeded_le_improved {n : ℕ} (hn : 1 < n) (hL : 240 ≤ Real.log n)
    (hU : Real.log n < 2000000000000) :
    Analysis.gaussianSeededSelected (Real.log n) ≤ improvedWitnessEnvelope n := by
  by_cases h : 240 < Real.log n
  · rw [improved_eq_gaussian hn h hU]
    exact Analysis.gaussianSeeded_selected_le_old (by linarith only [hL])
  · have h240 : Real.log n ≤ 240 := le_of_not_gt h
    rw [improved_eq_fixed35000 hn (by linarith only [hL, gammaSharpFixedSwitch_bounds.2]) h240]
    rw [Analysis.gaussianSeededSelected_eq_fixed
        (h240.trans Analysis.gaussianSeeded_switch35_bounds.1.le)]

/-- From L=240 to the triangular entrance, the seeded Gaussian interval formula is selected. -/
theorem next_eq_seeded {n : ℕ} (hn : 1 < n) (hL : 240 ≤ Real.log n)
    (hU : Real.log n < 1500000000000) :
    nextWitnessEnvelope n = Analysis.gaussianSeededSelected (Real.log n) := by
  have h100 : (100 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hc := Analysis.gaussianSeededSelected_linear hL
  apply le_antisymm (next_le_seeded h63)
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    exact seeded_le_improved hn hL (by linarith only [hU])
  · exact hc.le.trans (LLS.PaperStatements.pointwiseCutoff_linear_lower h100)
  · intro _; exact (Analysis.gaussianSeeded_lt_1000 hL).le
  · intro _; exact hc.le.trans (reflected_linear_lower (by linarith only [hL])).le
  · intro _; exact le_rfl
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- Between the triangular entrances the coefficient with its earlier domain is selected. -/
theorem next_eq_early {n : ℕ} (hn : 1 < n) (hL : 1500000000000 ≤ Real.log n)
    (hU : Real.log n < 2000000000000) :
    nextWitnessEnvelope n = (282924 / 1000000 : ℝ) * Real.log n ^ 2 := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h132 : (132 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hcoef : (282924 / 1000000 : ℝ) * Real.log n ^ 2 ≤ (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  have hcoefP : (282924 / 1000000 : ℝ) * Real.log n ^ 2 ≤ (16 / 25 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  apply le_antisymm (next_le_early hL)
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    rw [improved_eq_gaussian hn (by linarith only [hL]) hU]
    exact hcoef.trans (Analysis.gaussianFloorSelected_lower h63).le
  · exact hcoefP.trans (LLS.PaperStatements.pointwiseCutoff_linear_lower (by linarith only [hL]))
  · intro _; exact hcoef.trans (Analysis.gaussian1000_bound_lower h63).le
  · intro _; exact hcoefP.trans (reflected_linear_lower h132).le
  · intro _; exact hcoef.trans (Analysis.gaussianSeededSelected_lower h63).le
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro _; exact le_rfl
  · intro h; exfalso; linarith only [hU, h]

/-- Above the second triangular entrance the coefficient 0.2827 is selected. -/
theorem next_eq_triangular {n : ℕ} (hn : 1 < n) (hL : 2000000000000 ≤ Real.log n) :
    nextWitnessEnvelope n = (2827 / 10000 : ℝ) * Real.log n ^ 2 := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h132 : (132 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hcoef : (2827 / 10000 : ℝ) * Real.log n ^ 2 ≤ (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  have hcoefP : (2827 / 10000 : ℝ) * Real.log n ^ 2 ≤ (16 / 25 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  apply le_antisymm (next_le_triangular hL)
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    rw [improved_eq_triangular hn hL]
    exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  · exact hcoefP.trans (LLS.PaperStatements.pointwiseCutoff_linear_lower (by linarith only [hL]))
  · intro _; exact hcoef.trans (Analysis.gaussian1000_bound_lower h63).le
  · intro _; exact hcoefP.trans (reflected_linear_lower h132).le
  · intro _; exact hcoef.trans (Analysis.gaussianSeededSelected_lower h63).le
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro _; exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  · intro _; exact le_rfl

/-- Between L=100 and L=132 the remaining candidates are pointwise, reflected Gamma,
and the two-root Gaussian bound. The individual crossing order is not assumed. -/
theorem next_eq_middle_three {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n) (hU : Real.log n < 132) :
    nextWitnessEnvelope n =
      min (LLS.PaperStatements.pointwiseCutoff (Real.log n))
        (min (gammaReflectedBound (Real.log n)) (Analysis.gaussian1000Bound (Real.log n))) := by
  let C :=
    min (LLS.PaperStatements.pointwiseCutoff (Real.log n))
      (min (gammaReflectedBound (Real.log n)) (Analysis.gaussian1000Bound (Real.log n)))
  have hp : C ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := min_le_left _ _
  have hg : C ≤ gammaReflectedBound (Real.log n) := (min_le_right _ _).trans (min_le_left _ _)
  have ha : C ≤ Analysis.gaussian1000Bound (Real.log n) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply
    le_antisymm
      (le_min next_le_pointwise (le_min (next_le_reflected hL) (next_le_gaussian1000 h63)))
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL])]
    have hg1 := hg.trans (gammaReflected_lt_sharp hL).le
    by_cases h112 : Real.log n < 112
    · rw [improved_eq_middle_min hn hL h112]
      exact
        le_min
          (hp.trans (LLS.PaperStatements.pointwiseCutoff_lt_fourStep (by linarith only [hL])).le)
          hg1
    · rw [improved_eq_sharp hn (le_of_not_gt h112)
          (by linarith only [hU, gammaSharpFixedSwitch_bounds.1])]
      exact hg1
  · exact hp
  · intro _; exact ha
  · intro _; exact hg
  · intro h
    have hs : Real.log n ^ 2 < (35000 : ℝ) := by nlinarith only [hL, hU]
    exact
      hp.trans
        ((LLS.PaperStatements.pointwiseCutoff_lt_square (by linarith only [hL])).le.trans
          (hs.le.trans (seededSelected_floor h)))
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- From L=132 through L=235 only the pointwise and two-root Gaussian cutoffs remain. -/
theorem next_eq_middle_two {n : ℕ} (hn : 1 < n) (hL : 132 ≤ Real.log n) (hU : Real.log n ≤ 235) :
    nextWitnessEnvelope n =
      min (LLS.PaperStatements.pointwiseCutoff (Real.log n))
        (Analysis.gaussian1000Bound (Real.log n)) := by
  let C :=
    min (LLS.PaperStatements.pointwiseCutoff (Real.log n)) (Analysis.gaussian1000Bound (Real.log n))
  have hp : C ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := min_le_left _ _
  have ha : C ≤ Analysis.gaussian1000Bound (Real.log n) := min_le_right _ _
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply le_antisymm (le_min next_le_pointwise (next_le_gaussian1000 h63))
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL]), improved_eq_selected hn]
    exact ha.trans (gaussian1000_lt_improved hn hL hU).le
  · exact hp
  · intro _; exact ha
  · intro _; exact ha.trans (gaussian1000_lt_gammaReflected hL).le
  · intro h
    exact
      ha.trans
        ((Analysis.gaussian1000_lt_fixed (by linarith only [hL]) hU).le.trans
          (seededSelected_floor h))
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- Between L=235 and L=240 the only varying comparison is Gaussian1000 versus 35000. -/
theorem next_eq_fixed_gaussian {n : ℕ} (hn : 1 < n) (hL : 235 < Real.log n)
    (hU : Real.log n < 240) :
    nextWitnessEnvelope n = min 35000 (Analysis.gaussian1000Bound (Real.log n)) := by
  let C := min (35000 : ℝ) (Analysis.gaussian1000Bound (Real.log n))
  have hf : C ≤ (35000 : ℝ) := min_le_left _ _
  have ha : C ≤ Analysis.gaussian1000Bound (Real.log n) := min_le_right _ _
  have hbase :=
    improved_eq_fixed35000 hn (by linarith only [hL, gammaSharpFixedSwitch_bounds.2]) hU.le
  have hfixed : nextWitnessEnvelope n ≤ (35000 : ℝ) := by
    rw [← hbase]
    exact nextWitnessEnvelope_le_improved n
  have hs : (35000 : ℝ) < (16 / 25) * Real.log n ^ 2 := by nlinarith only [hL]
  apply le_antisymm (le_min hfixed (next_le_gaussian1000 (by linarith only [hL])))
  apply next_lower_of_candidates
  · rw [lowPrime_eq_improved_of_log (by linarith only [hL]), hbase]
    exact hf
  · exact
      hf.trans
        (hs.le.trans (LLS.PaperStatements.pointwiseCutoff_linear_lower (by linarith only [hL])))
  · intro _; exact ha
  · intro _; exact hf.trans (hs.le.trans (reflected_linear_lower (by linarith only [hL])).le)
  · intro h; exact hf.trans (seededSelected_floor h)
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hL, h]
  · intro h; exfalso; linarith only [hU, h]
  · intro h; exfalso; linarith only [hU, h]

/-- Exact public interval selection for the next envelope.
Unresolved comparisons remain only on the short stated pointwise/fixed and middle ranges.
The seeded function expands into its four exact floor/root pieces. -/
noncomputable def nextSelectedEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  let P := LLS.PaperStatements.pointwiseCutoff L
  let A := Analysis.gaussian1000Bound L
  if n < 3000 then smallIntervalBound n
  else
    if L ≤ 553 / 50 then lowPrimeSelected n
    else
      if L ≤ 11509 / 1000 then 61
      else
        if L ≤ 1179 / 100 then min 67 P
        else
          if L ≤ 1193 / 100 then min 71 P
          else
            if L ≤ 12337 / 1000 then min 73 P
            else
              if L < 100 then P
              else
                if L < 132 then min P (min (gammaReflectedBound L) A)
                else
                  if L ≤ 235 then min P A
                  else
                    if L < 240 then min 35000 A
                    else
                      if L < 1500000000000 then Analysis.gaussianSeededSelected L
                      else
                        if L < 2000000000000 then (282924 / 1000000) * L ^ 2
                        else (2827 / 10000) * L ^ 2

/-- The explicit interval selection equals the guarded candidate minimum for every n>1.
No primality, parity or GRH hypothesis is needed for this numerical identity. -/
theorem next_eq_selected {n : ℕ} (hn : 1 < n) : nextWitnessEnvelope n = nextSelectedEnvelope n := by
  by_cases hN : n < 3000
  · have hcast : (n : ℝ) ≤ 46000 := by
      exact_mod_cast (hN.le.trans (by norm_num only : 3000 ≤ 46000))
    have hL : Real.log n < 11 :=
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hcast).trans_lt
        Analysis.log_46000_lt_eleven
    rw [next_eq_low (by linarith only [hL]), lowPrime_eq_selected hn]
    simp only [nextSelectedEnvelope, lowPrimeSelected, ite_eq_left hN]
  · by_cases h0 : Real.log n ≤ 553 / 50
    · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_left h0]
      rw [next_eq_low h0, lowPrime_eq_selected hn]
    · by_cases h1 : Real.log n ≤ 11509 / 1000
      · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0, ite_eq_left h1]
        exact next_eq_fixed61 hn (le_of_not_gt hN) (lt_of_not_ge h0) h1
      · by_cases h2 : Real.log n ≤ 1179 / 100
        · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0, ite_eq_right h1,
            ite_eq_left h2]
          exact next_eq_min67 hn (lt_of_not_ge h1) h2
        · by_cases h3 : Real.log n ≤ 1193 / 100
          · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0, ite_eq_right h1,
              ite_eq_right h2, ite_eq_left h3]
            exact next_eq_min71 hn (lt_of_not_ge h2) h3
          · by_cases h4 : Real.log n ≤ 12337 / 1000
            · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0, ite_eq_right h1,
                ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
              exact next_eq_min73 hn (lt_of_not_ge h3) h4
            · by_cases h5 : Real.log n < 100
              · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0, ite_eq_right h1,
                  ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left h5]
                exact next_eq_pointwise hn (lt_of_not_ge h4) h5
              · by_cases h6 : Real.log n < 132
                · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0,
                    ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                    ite_eq_right h5, ite_eq_left h6]
                  exact next_eq_middle_three hn (le_of_not_gt h5) h6
                · by_cases h7 : Real.log n ≤ 235
                  · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0,
                      ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                      ite_eq_right h5, ite_eq_right h6, ite_eq_left h7]
                    exact next_eq_middle_two hn (le_of_not_gt h6) h7
                  · by_cases h8 : Real.log n < 240
                    · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0,
                        ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                        ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_left h8]
                      exact next_eq_fixed_gaussian hn (lt_of_not_ge h7) h8
                    · by_cases h9 : Real.log n < 1500000000000
                      · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0,
                          ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                          ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_right h8,
                          ite_eq_left h9]
                        exact next_eq_seeded hn (le_of_not_gt h8) h9
                      · by_cases h10 : Real.log n < 2000000000000
                        · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0,
                            ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                            ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_right h8,
                            ite_eq_right h9, ite_eq_left h10]
                          exact next_eq_early hn (le_of_not_gt h9) h10
                        · simp only [nextSelectedEnvelope, ite_eq_right hN, ite_eq_right h0,
                            ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
                            ite_eq_right h5, ite_eq_right h6, ite_eq_right h7, ite_eq_right h8,
                            ite_eq_right h9, ite_eq_right h10]
                          exact next_eq_triangular hn (le_of_not_gt h10)

/-- Under GRH, the exact selected envelope bounds an actual prime witness
for every odd composite n>1. Use the numerical selection identity. -/
theorem exists_prime_nextSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ nextSelectedEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← next_eq_selected hn]
  exact exists_prime_nextEnvelope hn ho hc hGRH

/-- Under GRH, the least rejecting prime satisfies the exact selected envelope
for every odd composite n>1, with no arithmetic branch assumptions. -/
theorem exists_least_nextSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ nextSelectedEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← next_eq_selected hn]
  exact exists_least_nextEnvelope hn ho hc hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
