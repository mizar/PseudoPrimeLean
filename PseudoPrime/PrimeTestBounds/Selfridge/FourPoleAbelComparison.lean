/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FourPoleAbelComparison
public import PseudoPrime.PrimeTestBounds.Selfridge.FourPoleAbelBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.PreciseSavingBounds

/-! # Final double-Abel Selfridge minima and whole-minimum comparisons

Negative and non-one stopping bounds retain their distinct preceding candidate sets.
The negative minimum absorbs exception 27 from endpoint three; the non-one bound keeps
an explicit maximum with exception 15. Empty domains have stopping bound zero and
classical trial bound one. The comparison leaf alone imports both the Abel and Q5
selection layers, so numerical changes do not propagate into their independent bases.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- The preceding negative stopping bound at a natural endpoint.
Use the complete Q5 minimum from three and zero on the empty domain.
Role: the full preceding baseline for negative stopping and trial comparisons. -/
noncomputable def previousNegStopBound (B : ℕ) : ℝ :=
  if B < 3 then 0 else PseudoSquare.preciseSavingEnvelope B

/-- The preceding non-one stopping bound with its distinct exceptional cap 15.
Use the complete guarded non-one minimum from three and zero below three.
Role: preserve dedicated non-one improvements in the Selfridge baseline. -/
noncomputable def previousNeStopBound (B : ℕ) : ℝ :=
  if B < 3 then 0 else max 15 (PseudoSquare.previousNonOneEnvelope B)

/-- The final negative stopping bound using the old minimum and the new Abel rows.
It equals the selected negative Jacobi envelope from three and zero below three.
Role: bound both scans while retaining the correct empty-domain convention. -/
noncomputable def abelNegStopBound (B : ℕ) : ℝ :=
  if B < 3 then 0 else PseudoSquare.fourPoleAbelNegEnvelope B

/-- The final non-one stopping bound using its complete old minimum and new Abel rows.
From three it retains exception 15 explicitly; below three it is zero.
Role: preserve the factor-detecting stopping meaning and its dedicated candidates. -/
noncomputable def abelNeStopBound (B : ℕ) : ℝ :=
  if B < 3 then 0 else max 15 (PseudoSquare.fourPoleAbelNeEnvelope B)

/-- The preceding negative classical trial bound with the totalized floor one.
Apply max(1,(X-3)/2) to the preceding negative stopping radius.
Role: compare sharp trial costs across the full natural endpoint domain. -/
noncomputable def previousNegTrialBound (B : ℕ) : ℝ :=
  max 1 ((previousNegStopBound B - 3) / 2)

/-- The preceding non-one trial bound obtained from its own stopping radius.
Apply max(1,(X-3)/2), preserving empty-domain trial one.
Role: the distinct non-one baseline for sharp trial comparisons. -/
noncomputable def previousNeTrialBound (B : ℕ) : ℝ :=
  max 1 ((previousNeStopBound B - 3) / 2)

/-- The final negative classical trial bound obtained from the selected stopping radius.
Apply max(1,(X-3)/2); the maximum disappears from endpoint three by the floor 27.
Role: transfer the analytic improvement to actual classical trial costs. -/
noncomputable def abelNegTrialBound (B : ℕ) : ℝ :=
  max 1 ((abelNegStopBound B - 3) / 2)

/-- The final non-one classical trial bound obtained from its selected stopping radius.
Apply max(1,(X-3)/2); exception 15 permits the sharp subtraction from endpoint three.
Role: preserve the non-one trial semantics and exact empty-domain count one. -/
noncomputable def abelNeTrialBound (B : ℕ) : ℝ :=
  max 1 ((abelNeStopBound B - 3) / 2)

/-- Below endpoint three the selected stopping bounds are zero and trial bounds one.
Unfold the definitions and evaluate the totalized sharp count formula.
Role: exact boundary behavior without applying an unguarded subtraction. -/
theorem abelSelection_empty {B : ℕ} (hB : B < 3) :
    abelNegStopBound B = 0 ∧
      abelNeStopBound B = 0 ∧ abelNegTrialBound B = 1 ∧ abelNeTrialBound B = 1 := by
  simp only [abelNegStopBound, abelNeStopBound, abelNegTrialBound, abelNeTrialBound, ite_eq_left hB]
  norm_num only
  exact ⟨True.intro, True.intro, max_eq_left (by norm_num only), max_eq_left (by norm_num only)⟩

/-- At every natural endpoint under GRH, both negative scans satisfy the final
negative bound and both non-one scans satisfy their separate final bound.
Use actual Jacobi maxima, their distinct exceptional caps and the exact empty boundary.
Role: connect both selected whole minima to all four actual stopping maxima. -/
theorem selfridgeMaxima_le_abelSelection (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤ abelNegStopBound B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ abelNegStopBound B ∧
      (classicalNeOneMaximum B : ℝ) ≤ abelNeStopBound B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ abelNeStopBound B := by
  by_cases hB : B < 3
  · have he := precise_empty_boundary hB
    have hb := abelSelection_empty hB
    simp only [he.1, he.2.1, he.2.2.1, he.2.2.2.1, hb.1, hb.2.1, Nat.cast_zero]
    exact ⟨le_refl 0, le_refl 0, le_refl 0, le_refl 0⟩
  · have hn :=
      selfridgeMaxima_le_of_QNegOne
        (PseudoSquare.fourPoleAbelNeg_ge_twenty_seven (Nat.le_of_not_lt hB))
        (PseudoSquare.QNegOne_le_fourPoleAbelEnvelope B hGRH)
    have he :=
      selfridgeNeOneMaxima_le_of_QNeOne_bound
        (le_max_left 15 (PseudoSquare.fourPoleAbelNeEnvelope B))
        ((PseudoSquare.QNeOne_le_fourPoleAbelEnvelope B hGRH).trans (le_max_right _ _))
    rw [abelNegStopBound, abelNeStopBound, ite_eq_right hB, ite_eq_right hB]
    exact ⟨hn.1, hn.2.1, he.1, he.2⟩

/-- Under GRH, both actual classical trial maxima obey their final selected bounds.
Apply the totalized sharp count transfer to the proved stopping bounds.
Role: the all-domain trial interface, including count one on empty domains. -/
theorem classicalTrials_le_abelSelection (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ abelNegTrialBound B ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ abelNeTrialBound B := by
  have hm := selfridgeMaxima_le_abelSelection B hGRH
  exact ⟨classicalTrialCount_real_max hm.1, classicalTrialCount_real_max hm.2.2.1⟩

/-- At every natural endpoint, all final stopping and trial bounds improve their
complete preceding counterparts. Use minimum projections and monotonicity of max
and the sharp affine trial formula. Role: unconditional whole-model non-worsening. -/
theorem abelSelection_nonworsening (B : ℕ) :
    abelNegStopBound B ≤ previousNegStopBound B ∧
      abelNeStopBound B ≤ previousNeStopBound B ∧
      abelNegTrialBound B ≤ previousNegTrialBound B ∧
      abelNeTrialBound B ≤ previousNeTrialBound B := by
  have hn : abelNegStopBound B ≤ previousNegStopBound B := by
    by_cases hB : B < 3
    · simp only [abelNegStopBound, previousNegStopBound, ite_eq_left hB, le_refl]
    · simp only [abelNegStopBound, previousNegStopBound, ite_eq_right hB]
      exact PseudoSquare.fourPoleAbelNeg_le_previous B
  have he : abelNeStopBound B ≤ previousNeStopBound B := by
    by_cases hB : B < 3
    · simp only [abelNeStopBound, previousNeStopBound, ite_eq_left hB, le_refl]
    · simp only [abelNeStopBound, previousNeStopBound, ite_eq_right hB]
      exact max_le_max (le_refl 15) (PseudoSquare.fourPoleAbelNe_le_previous B)
  exact
    ⟨hn, he,
      max_le_max (le_refl 1)
        (div_le_div_of_nonneg_right (sub_le_sub_right hn 3) (by norm_num only)),
      max_le_max (le_refl 1)
        (div_le_div_of_nonneg_right (sub_le_sub_right he 3) (by norm_num only))⟩

/-- From endpoint three both final trial bounds equal the sharp affine formulas.
The negative floor 27 and explicit non-one floor 15 make the outer floor one redundant.
Role: expose the exact analytic saving in each classical trial cost. -/
theorem abelTrialBounds_sharp {B : ℕ} (hB : 3 ≤ B) :
    abelNegTrialBound B = (PseudoSquare.fourPoleAbelNegEnvelope B - 3) / 2 ∧
      abelNeTrialBound B = (max 15 (PseudoSquare.fourPoleAbelNeEnvelope B) - 3) / 2 := by
  have hn := PseudoSquare.fourPoleAbelNeg_ge_twenty_seven hB
  have he := le_max_left 15 (PseudoSquare.fourPoleAbelNeEnvelope B)
  rw [abelNegTrialBound, abelNeTrialBound, abelNegStopBound, abelNeStopBound,
    ite_eq_right (Nat.not_lt.mpr hB), ite_eq_right (Nat.not_lt.mpr hB)]
  exact ⟨max_eq_right (by linarith only [hn]), max_eq_right (by linarith only [he])⟩

/-- From endpoint three under GRH, both actual classical trial maxima obey the
sharp subtraction formulas for their respective selected minima.
Rewrite the all-domain theorem using the certified floors. Role: sharp actual counts. -/
theorem classicalTrials_le_abelSharp {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleAbelNegEnvelope B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤
        (max 15 (PseudoSquare.fourPoleAbelNeEnvelope B) - 3) / 2 := by
  have h := classicalTrials_le_abelSelection B hGRH
  rw [(abelTrialBounds_sharp hB).1] at h
  rw [(abelTrialBounds_sharp hB).2] at h
  exact h

/-- For endpoint logarithms between four million and ten million, both final
stopping bounds and both final trial bounds strictly improve the full old minima.
Use the continuous whole-minimum Jacobi comparison, retain exception 15 and remove
the inactive trial floor one. Role: strict savings for both semantics and both scans. -/
theorem abelSelection_strict_window {B : ℕ} (hL : 4000000 ≤ Real.log B)
    (hU : Real.log B ≤ 10000000) :
    abelNegStopBound B < previousNegStopBound B ∧
      abelNeStopBound B < previousNeStopBound B ∧
      abelNegTrialBound B < previousNegTrialBound B ∧
      abelNeTrialBound B < previousNeTrialBound B := by
  have hp : 0 < Real.log B := (by norm_num only : (0 : ℝ) < 4000000).trans_le hL
  have hb0 : 0 < B := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.cast_zero, Real.log_zero] at hp
    exact (lt_irrefl 0) hp
  have hlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hb0 : (0 : ℝ) < B)
  have hB : 3 ≤ B := Nat.cast_le.mp (by linarith only [hL, hlog] : (3 : ℝ) ≤ B)
  have hsmall := Nat.not_lt.mpr hB
  have hs := PseudoSquare.fourPoleAbel_strict_window hL hU
  have hsq := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 4000000) (Real.log_natCast_nonneg B)).mpr hL
  have h15 : (15 : ℝ) < PseudoSquare.previousNonOneEnvelope B := by
    rw [PseudoSquare.abel_previous_nonOne_window hL hU]
    nlinarith only [hsq]
  have hn : abelNegStopBound B < previousNegStopBound B := by
    rw [abelNegStopBound, previousNegStopBound, ite_eq_right hsmall, ite_eq_right hsmall]
    exact hs.1
  have he : abelNeStopBound B < previousNeStopBound B := by
    rw [abelNeStopBound, previousNeStopBound, ite_eq_right hsmall, ite_eq_right hsmall,
      max_eq_right h15.le]
    exact max_lt h15 hs.2
  have hn5 : (5 : ℝ) ≤ previousNegStopBound B := by
    rw [previousNegStopBound, ite_eq_right hsmall, PseudoSquare.abel_previous_negative_window hL hU]
    nlinarith only [hsq]
  have he5 : (5 : ℝ) ≤ previousNeStopBound B := by
    rw [previousNeStopBound, ite_eq_right hsmall]
    exact (by norm_num only : (5 : ℝ) ≤ 15).trans (le_max_left _ _)
  have hnt : abelNegTrialBound B < previousNegTrialBound B := by
    rw [(abelTrialBounds_sharp hB).1, previousNegTrialBound,
      max_eq_right (by linarith only [hn5] : (1 : ℝ) ≤ (previousNegStopBound B - 3) / 2)]
    rw [abelNegStopBound, ite_eq_right hsmall] at hn
    linarith only [hn]
  have het : abelNeTrialBound B < previousNeTrialBound B := by
    rw [(abelTrialBounds_sharp hB).2, previousNeTrialBound,
      max_eq_right (by linarith only [he5] : (1 : ℝ) ≤ (previousNeStopBound B - 3) / 2)]
    rw [abelNeStopBound, ite_eq_right hsmall] at he
    linarith only [he]
  exact ⟨hn, he, hnt, het⟩

end PseudoPrime.PrimeTestBounds.Selfridge
