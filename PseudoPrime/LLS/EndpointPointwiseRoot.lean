/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwise

/-! # Monotone pointwise endpoint correction and its inverse radius -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Polynomial extra numerator retained by the pointwise Riemann reciprocal loss. -/
noncomputable def pointwiseExtra (y : ℝ) : ℝ :=
  36620000 * (y + 1 + Real.log y) * ((33 / 100000 : ℝ) * y ^ 2 - 231 / 5000 * y + 16033 / 9000)

/-- Function-level form of the extra numerator, for explicit derivative rules. -/
noncomputable def pointwiseExtraFunction : ℝ → ℝ :=
  (fun x : ℝ => 36620000 * (x + 1 + Real.log x)) *
    (fun x => (33 / 100000 : ℝ) * x ^ 2 - 231 / 5000 * x + 16033 / 9000)

/-- Pointwise endpoint correction as the collected diagonal gap divided by its denominator.
For y>=8 this equals the previous correction plus the positive reciprocal improvement. -/
noncomputable def pointwiseCorrection (y : ℝ) : ℝ :=
  (fullEndpointEvenGapCorrectionNumerator y + pointwiseExtra y) /
    (18310000 * fullEndpointEvenGapDenominator y)

/-- The pointwise increase in the normalized diagonal gap. -/
noncomputable def pointwiseDelta (y : ℝ) : ℝ :=
  2 * y ^ 2 * (y + 1 + Real.log y) * ((31551 / 20000 : ℝ) - Analysis.pointwiseReciprocalLoss y) /
    fullEndpointEvenGapDenominator y

/-- The pointwise correction adds the positive reciprocal improvement. -/
theorem pointwiseCorrection_eq {y : ℝ} (hy : 8 ≤ y) :
    pointwiseCorrection y = fullEndpointEvenGapCorrection y + pointwiseDelta y := by
  have hy0 : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hD := ne_of_gt (fullEndpointEvenGapDenominator_pos hy)
  dsimp only [pointwiseCorrection, pointwiseDelta, fullEndpointEvenGapCorrection, pointwiseExtra,
    Analysis.pointwiseReciprocalLoss]
  field_simp [hy0, hD]
  ring

/-- Normalizing the existing pointwise gap gives the exact correction at every level. -/
theorem pointwiseGap_eq {L y : ℝ} (hy : 8 ≤ y) :
    endpointPointwiseGap L (2096 / 1831) y (Real.log y) =
      fullEndpointEvenGapDenominator y * (y + pointwiseCorrection y - L) := by
  rw [pointwiseCorrection_eq hy]
  dsimp only [endpointPointwiseGap]
  rw [fullEndpointEvenExactComparisonGap_eq_denominator_correction hy]
  have hD := ne_of_gt (fullEndpointEvenGapDenominator_pos hy)
  dsimp only [pointwiseDelta]
  field_simp [hD]
  ring

/-- The retained reciprocal improvement is strictly positive. -/
theorem pointwiseDelta_pos {y : ℝ} (hy : 8 ≤ y) : 0 < pointwiseDelta y := by
  have hy0 : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hid :
    (31551 / 20000 : ℝ) - Analysis.pointwiseReciprocalLoss y =
      1221 / 40082500 + 16033 / 9000 * (1 / y - 2079 / 160330) ^ 2 := by
    dsimp only [Analysis.pointwiseReciprocalLoss]
    field_simp [hy0]
    ring
  have hg : (0 : ℝ) < 31551 / 20000 - Analysis.pointwiseReciprocalLoss y := by
    rw [hid]
    nlinarith only [sq_nonneg (1 / y - 2079 / 160330)]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  apply div_pos _ (fullEndpointEvenGapDenominator_pos hy)
  exact
    mul_pos
      (mul_pos (mul_pos (by norm_num only) (sq_pos_of_pos (by linarith only [hy])))
        (by linarith only [hy, hz]))
      hg

/-- Positive shifted coefficients in the pointwise correction derivative. -/
noncomputable def pointwiseQ2 (y : ℝ) : ℝ :=
  (12 : ℝ) * (y - 2) ^ 4 + (904571 / 12500 : ℝ) * (y - 2) ^ 3 +
    (9374317 / 56250 : ℝ) * (y - 2) ^ 2 +
    (4949992 / 28125 : ℝ) * (y - 2) ^ 1 +
    (677876 / 9375 : ℝ)

/-- The shifted polynomial is positive for y>=2, since every coefficient is positive. -/
theorem pointwiseQ2_pos {y : ℝ} (hy : 2 ≤ y) : 0 < pointwiseQ2 y := by
  have hu : 0 ≤ y - 2 := sub_nonneg.mpr hy
  dsimp only [pointwiseQ2]
  nlinarith only [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5]

/-- Positive shifted coefficients in the pointwise correction derivative. -/
noncomputable def pointwiseQ1 (y : ℝ) : ℝ :=
  (95239 / 25000 : ℝ) * (y - 2) ^ 5 + (585527 / 12500 : ℝ) * (y - 2) ^ 4 +
    (9298789 / 45000 : ℝ) * (y - 2) ^ 3 +
    (1309722 / 3125 : ℝ) * (y - 2) ^ 2 +
    (4922181 / 12500 : ℝ) * (y - 2) ^ 1 +
    (7911799 / 56250 : ℝ)

/-- The shifted polynomial is positive for y>=2, since every coefficient is positive. -/
theorem pointwiseQ1_pos {y : ℝ} (hy : 2 ≤ y) : 0 < pointwiseQ1 y := by
  have hu : 0 ≤ y - 2 := sub_nonneg.mpr hy
  dsimp only [pointwiseQ1]
  nlinarith only [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5]

/-- Positive shifted coefficients in the pointwise correction derivative. -/
noncomputable def pointwiseQ0 (y : ℝ) : ℝ :=
  (214871 / 25000 : ℝ) * (y - 2) ^ 5 + (17892509 / 225000 : ℝ) * (y - 2) ^ 4 +
    (21290683 / 75000 : ℝ) * (y - 2) ^ 3 +
    (21829787 / 45000 : ℝ) * (y - 2) ^ 2 +
    (174983 / 450 : ℝ) * (y - 2) ^ 1 +
    (1097594 / 9375 : ℝ)

/-- The shifted polynomial is positive for y>=2, since every coefficient is positive. -/
theorem pointwiseQ0_pos {y : ℝ} (hy : 2 ≤ y) : 0 < pointwiseQ0 y := by
  have hu : 0 ≤ y - 2 := sub_nonneg.mpr hy
  dsimp only [pointwiseQ0]
  nlinarith only [hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5]

/-- Collected numerator for the derivative of the pointwise correction. -/
noncomputable def pointwiseDerivativeNumerator (y z : ℝ) : ℝ :=
  (2 * y ^ 5 + 4 * y * (y - 1) ^ 2 * z) * (y - z ^ 2) + pointwiseQ2 y * z ^ 2 + pointwiseQ1 y * z +
    pointwiseQ0 y

/-- The extra polynomial has an explicit elementary logarithmic derivative. -/
theorem pointwiseExtra_deriv {y : ℝ} (hy : 8 ≤ y) :
    deriv pointwiseExtra y =
      36620000 * (1 + 1 / y) * ((33 / 100000 : ℝ) * y ^ 2 - 231 / 5000 * y + 16033 / 9000) +
        36620000 * (y + 1 + Real.log y) * (33 / 50000 * y - 231 / 5000) := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have h1 :=
    (((hasDerivAt_id y).add_const 1).add (Real.hasDerivAt_log hyne)).const_mul (36620000 : ℝ)
  have h2 :=
    (((hasDerivAt_id y).pow 2).const_mul (33 / 100000 : ℝ)).sub
      ((hasDerivAt_id y).const_mul (231 / 5000 : ℝ))
  have h := (h1.mul (h2.add_const (16033 / 9000 : ℝ))).deriv
  change
    deriv pointwiseExtra y =
      36620000 * (1 + y⁻¹) * ((33 / 100000 : ℝ) * y ^ 2 - 231 / 5000 * y + 16033 / 9000) +
        36620000 * (y + 1 + Real.log y) *
          (33 / 100000 * ((2 : ℝ) * y ^ (2 - 1) * 1) - 231 / 5000 * 1) at h
  convert h using 1
  ring

/-- The pointwise correction is differentiable throughout the radius domain. -/
theorem pointwiseCorrection_differentiable {y : ℝ} (hy : 8 ≤ y) :
    DifferentiableAt ℝ pointwiseCorrection y := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hM : DifferentiableAt ℝ fullEndpointEvenGapCorrectionNumeratorFunction y := by
    unfold fullEndpointEvenGapCorrectionNumeratorFunction
    fun_prop (disch := exact hyne)
  have hE : DifferentiableAt ℝ pointwiseExtraFunction y := by
    unfold pointwiseExtraFunction
    fun_prop (disch := exact hyne)
  have hD := (fullEndpointEvenGapDenominator_differentiableAt hy).const_mul (18310000 : ℝ)
  exact
    (hM.add hE).div hD
      (ne_of_gt (mul_pos (by norm_num only) (fullEndpointEvenGapDenominator_pos hy)))

/-- Its derivative is the positive polynomial numerator over y times the squared gap denominator. -/
theorem pointwiseCorrection_deriv {y : ℝ} (hy : 8 ≤ y) :
    deriv pointwiseCorrection y =
      pointwiseDerivativeNumerator y (Real.log y) / (y * fullEndpointEvenGapDenominator y ^ 2) := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hM : DifferentiableAt ℝ fullEndpointEvenGapCorrectionNumeratorFunction y := by
    unfold fullEndpointEvenGapCorrectionNumeratorFunction
    fun_prop (disch := exact hyne)
  have hE : DifferentiableAt ℝ pointwiseExtraFunction y := by
    unfold pointwiseExtraFunction
    fun_prop (disch := exact hyne)
  have hD := fullEndpointEvenGapDenominator_differentiableAt hy
  have hden :=
    ne_of_gt
      (mul_pos (by norm_num only : (0 : ℝ) < 18310000) (fullEndpointEvenGapDenominator_pos hy))
  change
    deriv
        ((fullEndpointEvenGapCorrectionNumeratorFunction + pointwiseExtraFunction) /
          (fun x => 18310000 * fullEndpointEvenGapDenominator x))
        y =
      _
  rw [deriv_div (hM.add hE) (hD.const_mul 18310000) hden, deriv_add hM hE,
    deriv_const_mul 18310000 hD]
  change
    ((deriv (fun x => fullEndpointEvenGapCorrectionNumerator x) y + deriv pointwiseExtra y) *
            (18310000 * fullEndpointEvenGapDenominator y) -
          (fullEndpointEvenGapCorrectionNumerator y + pointwiseExtra y) *
            (18310000 * deriv (fun x => fullEndpointEvenGapDenominator x) y)) /
        (18310000 * fullEndpointEvenGapDenominator y) ^ 2 =
      _
  rw [deriv_fullEndpointEvenGapCorrectionNumerator hy, pointwiseExtra_deriv hy,
    deriv_fullEndpointEvenGapDenominator hy]
  have hDne := ne_of_gt (fullEndpointEvenGapDenominator_pos hy)
  dsimp only [fullEndpointEvenGapDenominator] at hDne ⊢
  dsimp only [fullEndpointEvenGapCorrectionNumerator, pointwiseExtra, pointwiseDerivativeNumerator,
    pointwiseQ2, pointwiseQ1, pointwiseQ0]
  field_simp [hyne, hDne]
  ring

/-- The collected derivative numerator is positive from radius eight onward. -/
theorem pointwiseDerivativeNumerator_pos {y : ℝ} (hy : 8 ≤ y) :
    0 < pointwiseDerivativeNumerator y (Real.log y) := by
  have hypos : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have ha : 0 ≤ 2 * y ^ 5 + 4 * y * (y - 1) ^ 2 * Real.log y :=
    add_nonneg (mul_nonneg (by norm_num only) (pow_nonneg hypos.le 5))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hypos.le) (sq_nonneg _)) hz)
  have hm := mul_nonneg ha (sub_nonneg.mpr (log_sq_le_self_of_eight_le hy))
  have h2 :=
    mul_nonneg (pointwiseQ2_pos (by linarith only [hy] : 2 ≤ y)).le (sq_nonneg (Real.log y))
  have h1 := mul_nonneg (pointwiseQ1_pos (by linarith only [hy] : 2 ≤ y)).le hz
  exact
    add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg hm h2) h1)
      (pointwiseQ0_pos (by linarith only [hy]))

/-- The pointwise correction is strictly increasing on its radius domain. -/
theorem pointwiseCorrection_strictMonoOn : StrictMonoOn pointwiseCorrection (Set.Ici (8 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (8 : ℝ))
  · intro y hy
    exact (pointwiseCorrection_differentiable hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    change (8 : ℝ) < y at hy
    rw [pointwiseCorrection_deriv hy.le]
    exact
      div_pos (pointwiseDerivativeNumerator_pos hy.le)
        (mul_pos (by linarith only [hy]) (sq_pos_of_pos (fullEndpointEvenGapDenominator_pos hy.le)))

/-- The scalar level map whose inverse supplies the pointwise radius. -/
noncomputable def pointwiseLevel (y : ℝ) : ℝ :=
  y + pointwiseCorrection y

/-- The level map is strictly increasing from radius eight onward. -/
theorem pointwiseLevel_strictMonoOn : StrictMonoOn pointwiseLevel (Set.Ici (8 : ℝ)) := by
  intro x hx y hy hxy
  exact add_lt_add hxy (pointwiseCorrection_strictMonoOn hx hy hxy)

/-- The pointwise correction is positive throughout its radius domain. -/
theorem pointwiseCorrection_pos {y : ℝ} (hy : 8 ≤ y) : 0 < pointwiseCorrection y := by
  rw [pointwiseCorrection_eq hy]
  have hh := fullEndpointEvenGapCorrection_gt_16over5 hy
  have hd := pointwiseDelta_pos hy
  linarith only [hh, hd]

/-- At the floor radius the pointwise correction is below 3.3. -/
theorem pointwiseCorrection_eight_lt : pointwiseCorrection 8 < (33 / 10 : ℝ) := by
  rw [pointwiseCorrection_eq (by norm_num only : (8 : ℝ) ≤ 8)]
  have hd : pointwiseDelta 8 < (1 / 20 : ℝ) := by
    apply (div_lt_iff₀ (fullEndpointEvenGapDenominator_pos (by norm_num only))).mpr
    norm_num only [Analysis.pointwiseReciprocalLoss, fullEndpointEvenGapDenominator]
    have hz : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num only)
    linarith only [hz]
  linarith only [correction_eight_lt, hd]

/-- Above the floor level there is exactly one radius at least eight with level L. -/
theorem pointwiseLevel_solution {L : ℝ} (hL : pointwiseLevel 8 < L) :
    ∃! y : ℝ, 8 ≤ y ∧ pointwiseLevel y = L := by
  have h8 : (8 : ℝ) < L := by
    have hp := pointwiseCorrection_pos (by norm_num only : (8 : ℝ) ≤ 8)
    dsimp only [pointwiseLevel] at hL
    linarith only [hL, hp]
  have hc : ContinuousOn pointwiseLevel (Set.Icc 8 L) := by
    intro y hy
    exact
      (differentiableAt_id.add
          (pointwiseCorrection_differentiable hy.1)).continuousAt.continuousWithinAt
  have htop : L ≤ pointwiseLevel L := by
    have hp := pointwiseCorrection_pos h8.le
    dsimp only [pointwiseLevel]
    linarith only [hp]
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc h8.le hc ⟨hL.le, htop⟩
  refine ⟨y, ⟨hy.1, he⟩, ?_⟩
  intro z hz
  exact pointwiseLevel_strictMonoOn.injOn hz.1 hy.1 (hz.2.trans he.symm)

/-- The inverse level radius, clipped to eight below its entrance level.
Existence and uniqueness follow from continuity and strict monotonicity on [8,infinity). -/
noncomputable def pointwiseRadius (L : ℝ) : ℝ :=
  if h : pointwiseLevel 8 < L then Classical.choose (pointwiseLevel_solution h).exists else 8

/-- The squared inverse radius gives the all-input pointwise witness cutoff. -/
noncomputable def pointwiseCutoff (L : ℝ) : ℝ :=
  pointwiseRadius L ^ 2

/-- The inverse radius remains at least eight and its level is at least L.
It equals eight or solves the level equation exactly. -/
theorem pointwiseRadius_spec (L : ℝ) :
    8 ≤ pointwiseRadius L ∧
      L ≤ pointwiseLevel (pointwiseRadius L) ∧
      (pointwiseRadius L = 8 ∨ pointwiseLevel (pointwiseRadius L) = L) := by
  by_cases h : pointwiseLevel 8 < L
  · have hs := Classical.choose_spec (pointwiseLevel_solution h).exists
    rw [pointwiseRadius, dite_eq_left h]
    exact ⟨hs.1, hs.2.ge, Or.inr hs.2⟩
  · rw [pointwiseRadius, dite_eq_right h]
    exact ⟨le_rfl, le_of_not_gt h, Or.inl rfl⟩

/-- The clipped inverse radius is monotone on all real levels. -/
theorem pointwiseRadius_mono : Monotone pointwiseRadius := by
  intro L K hLK
  have hs := pointwiseRadius_spec L
  have ht := pointwiseRadius_spec K
  rcases hs.2.2 with he | he
  · rw [he]
    exact ht.1
  · by_contra hn
    have hm := pointwiseLevel_strictMonoOn ht.1 hs.1 (lt_of_not_ge hn)
    rw [he] at hm
    exact not_lt.mpr (hLK.trans ht.2.1) hm

/-- Every radius strictly above the inverse radius has positive pointwise gap. -/
theorem pointwise_gap_above {L y : ℝ} (hy : pointwiseRadius L < y) :
    0 < endpointPointwiseGap L (2096 / 1831) y (Real.log y) := by
  have hs := pointwiseRadius_spec L
  have hy8 := hs.1.trans hy.le
  rw [pointwiseGap_eq hy8]
  have hm := pointwiseLevel_strictMonoOn hs.1 hy8 hy
  exact mul_pos (fullEndpointEvenGapDenominator_pos hy8) (sub_pos.mpr (hs.2.1.trans_lt hm))

/-- Strictly increasing the level of a radius places the inverse strictly below it,
provided the tested radius exceeds the floor. -/
theorem pointwiseRadius_lt_of_level {L y : ℝ} (hy : 8 < y) (hL : L < pointwiseLevel y) :
    pointwiseRadius L < y := by
  have hs := pointwiseRadius_spec L
  rcases hs.2.2 with he | he
  · rw [he]
    exact hy
  · by_contra hn
    have hm := pointwiseLevel_strictMonoOn.monotoneOn hy.le hs.1 (le_of_not_gt hn)
    rw [he] at hm
    exact not_le.mpr hL hm

/-- From L>=45/4, the inverse pointwise cutoff is strictly below the four-step cutoff.
The four-step radius is above eight and has strictly positive existing endpoint gap. -/
theorem pointwiseCutoff_lt_fourStep {L : ℝ} (hL : 45 / 4 ≤ L) :
    pointwiseCutoff L < endpointFourStepCutoff L := by
  have hd : (8 : ℝ) < endpointFourthRadius L :=
    (le_max_left _ _).trans_lt (endpoint_fourth_bounds hL).1
  have hg := endpoint_fourStep_gap hL
  rw [fullEndpointEvenExactComparisonGap_eq_denominator_correction hd.le] at hg
  have hf :
    0 < endpointFourthRadius L + fullEndpointEvenGapCorrection (endpointFourthRadius L) - L :=
    pos_of_mul_pos_right hg (fullEndpointEvenGapDenominator_pos hd.le).le
  have he := pointwiseCorrection_eq hd.le
  have hp := pointwiseDelta_pos hd.le
  have hl : L < pointwiseLevel (endpointFourthRadius L) := by
    dsimp only [pointwiseLevel]
    linarith only [hf, he, hp]
  exact
    (sq_lt_sq₀ (by linarith only [(pointwiseRadius_spec L).1] : 0 ≤ pointwiseRadius L)
          (by linarith only [hd] : 0 ≤ endpointFourthRadius L)).mpr
      (pointwiseRadius_lt_of_level hd hl)

end PseudoPrime.LLS.PaperStatements
