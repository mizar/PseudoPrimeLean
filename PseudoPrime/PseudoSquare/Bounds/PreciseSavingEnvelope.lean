/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.PreciseSavingCumulative
public import PseudoPrime.PseudoSquare.Bounds.PreciseSavingWindowBounds
public import PseudoPrime.PseudoSquare.Bounds.FiniteEndpointBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaCommonBounds
public import PseudoPrime.PseudoSquare.Bounds.FourPoleReducedBounds
public import PseudoPrime.PseudoSquare.Bounds.QuarterLogClippedNegOneBounds

/-! # The precise-saving envelope and the complete preceding negative minimum

The preceding envelope retains the finite guards, all common-endpoint candidates and
the clipped two-pole branch from logarithmic scale five hundred. The pointwise regime
branches in the preceding plot are already represented by these common candidates.
The fourth-pole term uses the preceding three certified rows. New Abel rows are combined
by their later consumer rather than introduced into this baseline model.

Ra and R31 are intersected with that complete baseline. The continuous window forty-four
through forty-six reduces the preceding minimum to 4093 and bounds R31 below 3969.
Dedicated non-one candidates and factor-aware pointwise cutoffs are not substituted into
this cumulative negative minimum.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The complete preceding factor-independent negative-witness candidate minimum.
Input: any natural endpoint. Output: the finite/common, Gamma and three-row fourth-pole minimum.
The clipped two-pole term retains its original guard at logarithmic scale five hundred.
Role: an explicit baseline for non-worsening and whole-minimum strict comparisons. -/
noncomputable def previousNegativeEnvelope (B : ℕ) : ℝ :=
  min (negOneEndpointEnvelope B)
    (min (mixedScaleBound B)
      (min (negativeScaleBound B)
        (min (fourPoleReducedBound B)
          (if 500 ≤ Real.log B then quarterClippedTwoPoleNegOneRadius (Real.log B)
          else negOneEndpointEnvelope B))))

/-- Intersect the complete preceding negative minimum with the two precise-saving radii.
Input: any natural endpoint. Output: the smallest cumulative candidate, preserving all old guards.
Role: improve the negative public bound while retaining dedicated non-one bounds separately. -/
noncomputable def preciseSavingEnvelope (B : ℕ) : ℝ :=
  min (previousNegativeEnvelope B) (min (preciseElementaryRadius B) (prime31SavingRadius B))

/-- The finite/common negative endpoint is nonnegative even on an empty domain.
Input: any endpoint. Claim: each square, joint candidate and guarded finite cap is nonnegative.
Proof: combine their explicit lower bounds. Role: full-domain cumulative lifting. -/
private theorem previous_finite_nonneg (B : ℕ) : 0 ≤ negOneEndpointEnvelope B := by
  have hj : (0 : ℝ) ≤ jointEndpointBound B :=
    mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9999 / 10000) (sq_nonneg _)
  have hf : (0 : ℝ) ≤ if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B := by
    by_cases h : Real.log B ≤ 1609 / 25
    · rw [ite_eq_left h]
      norm_num only
    · rw [ite_eq_right h]
      exact hj
  have hc : (0 : ℝ) ≤ commonEndpointEnvelope B := le_min (sq_nonneg _) (le_min hj hf)
  apply le_min hc
  by_cases h : B < 750
  · rw [ite_eq_left h]
    norm_num only
  · rw [ite_eq_right h]
    exact hc

/-- The complete preceding minimum is nonnegative on every natural endpoint.
Input: any endpoint. Claim: the guarded minimum covers an empty witness maximum.
Proof: positivity of the coefficients and squared radii.
Role: extend the preceding cumulative witness interface to endpoints below three. -/
theorem previousNegativeEnvelope_nonneg (B : ℕ) : 0 ≤ previousNegativeEnvelope B := by
  have hf := previous_finite_nonneg B
  have hm : (0 : ℝ) ≤ mixedScaleBound B :=
    logScaleBound_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 100) 290 B
  have hn : (0 : ℝ) ≤ negativeScaleBound B :=
    logScaleBound_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) 46000 B
  have hk := (by norm_num only : (0 : ℝ) ≤ 27).trans (fourPole_reduced_ge_twenty_seven B)
  have hq :
    (0 : ℝ) ≤
      if 500 ≤ Real.log B then quarterClippedTwoPoleNegOneRadius (Real.log B)
      else negOneEndpointEnvelope B := by
    by_cases h : 500 ≤ Real.log B
    · rw [ite_eq_left h]
      exact mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (sq_nonneg _)
    · rw [ite_eq_right h]
      exact hf
  exact le_min hf (le_min hm (le_min hn (le_min hk hq)))

/-- Under GRH the complete preceding minimum bounds every natural negative-witness maximum.
Input: any natural endpoint and GRH. Claim: all preceding active branches remain valid.
Proof: combine their actual cumulative APIs, treating the empty domain explicitly.
Role: retain the full old candidate set before adding the precise-saving radii. -/
theorem QNegOne_le_previousNegative (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ previousNegativeEnvelope B := by
  by_cases hB : 3 ≤ B
  · have hf := QNegOne_le_endpoint hB hGRH
    have hq :
      (QNegOne B : ℝ) ≤
        if 500 ≤ Real.log B then quarterClippedTwoPoleNegOneRadius (Real.log B)
        else negOneEndpointEnvelope B := by
      by_cases h : 500 ≤ Real.log B
      · rw [ite_eq_left h]
        exact QNegOne_le_quarterClippedTwoPole_logarithmic h hGRH
      · rw [ite_eq_right h]
        exact hf
    exact
      le_min hf
        (le_min (QNegOne_le_mixed_scale B hGRH)
          (le_min (QNegOne_le_smoothed_scale B hGRH)
            (le_min (QNegOne_le_fourPole_reduced B hGRH) hq)))
  · rw [(witnessMaxima_eq_zero_of_small (Nat.lt_of_not_ge hB)).1, Nat.cast_zero]
    exact previousNegativeEnvelope_nonneg B

/-- Under GRH the new precise-saving minimum bounds the negative maximum at every endpoint.
Input: any natural endpoint and GRH. Claim: the full new cumulative envelope is valid.
Proof: intersect the preceding minimum with both proved radius estimates.
Role: the public negative-witness bound, with no factorization or extra scalar premise. -/
theorem QNegOne_le_preciseSaving (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ preciseSavingEnvelope B :=
  le_min (QNegOne_le_previousNegative B hGRH)
    (le_min (QNegOne_le_preciseRadii B hGRH).1 (QNegOne_le_preciseRadii B hGRH).2)

/-- Both Jacobi maxima satisfy the new negative envelope under GRH.
Input: any endpoint and GRH. Claim: inclusion transfers the negative bound to non-one witnesses.
Proof: compare the natural maxima.
Role: a valid transfer without replacing dedicated non-one APIs. -/
theorem witnessMaxima_le_preciseSaving (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ preciseSavingEnvelope B ∧ (QNeOne B : ℝ) ≤ preciseSavingEnvelope B :=
  ⟨QNegOne_le_preciseSaving B hGRH,
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_preciseSaving B hGRH)⟩

/-- The new cumulative envelope never worsens the complete preceding minimum.
Input: any endpoint. Claim: the new value is no larger than the old candidate minimum.
Proof: the left minimum comparison. Role: unconditional scalar non-worsening. -/
theorem preciseSavingEnvelope_le_previous (B : ℕ) :
    preciseSavingEnvelope B ≤ previousNegativeEnvelope B :=
  min_le_left _ _

/-- The new envelope also retains the full cutoff-thirty-one radius improvement.
Input: any endpoint. Claim: the envelope does not exceed R31.
Proof: project twice from the minimum. Role: the certified winning-window comparison. -/
theorem preciseSavingEnvelope_le_prime31 (B : ℕ) :
    preciseSavingEnvelope B ≤ prime31SavingRadius B :=
  (min_le_right _ _).trans (min_le_right _ _)

/-- The precise-saving envelope is nonnegative on every endpoint.
Input: any endpoint. Claim: the intersected candidate still covers an empty maximum.
Proof: all three arguments of the minimum are nonnegative.
Role: exact empty-domain Selfridge transfer without padding the Jacobi radius. -/
theorem preciseSavingEnvelope_nonneg (B : ℕ) : 0 ≤ preciseSavingEnvelope B :=
  le_min (previousNegativeEnvelope_nonneg B) (le_min (sq_nonneg _) (sq_nonneg _))

/-- The least actual negative witness obeys the complete new envelope under GRH.
Input: an odd nonsquare, GRH and witness nonemptiness. Claim: all selected bounds hold together.
Proof: embed that input in its endpoint maximum.
Role: pointwise counterpart of the public minimum. -/
theorem leastWitness_le_preciseEnvelope {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ preciseSavingEnvelope n :=
  (Nat.cast_le.mpr
        (primeNegOneWitness_le_QNegOne
          (NumberTheory.mem_admissibleFinset_iff.mpr ⟨hn.pos, le_rfl, hn, hns⟩))).trans
    (QNegOne_le_preciseSaving n hGRH)

/-- An actual odd-prime negative witness satisfies the full precise-saving envelope.
Input: an odd nonsquare and GRH. Claim: the witness set has a member within the new minimum.
Proof: choose the bounded least witness.
Role: a closed actual-prime interface for the public bound. -/
theorem existsWitness_le_preciseEnvelope {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ preciseSavingEnvelope n :=
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  ⟨NumberTheory.primeNegOneWitness n hw, NumberTheory.primeNegOneWitness_mem n hw,
    leastWitness_le_preciseEnvelope hn hns hGRH hw⟩

/-- At a positive natural endpoint the original quadratic logarithm splits exactly.
Input: a positive endpoint. Claim: log(4B)=log(B)+log(4).
Proof: normalize the natural cast and split the product logarithm.
Role: connect the numerical window certificates to the actual radius definitions. -/
private theorem precise_level_log_split {B : ℕ} (hB : 0 < B) :
    Real.log (4 * B : ℕ) = Real.log B + Real.log 4 := by
  rw [Nat.cast_mul, Nat.cast_ofNat,
    Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hB).ne',
    add_comm (Real.log (4 : ℝ))]

/-- A logarithmic endpoint at least forty-four is positive.
Input: that lower logarithmic bound. Claim: the natural endpoint is nonzero.
Proof: exclude the totalized value log(0)=0.
Role: justify the original-level logarithm identity inside the comparison window. -/
private theorem precise_window_positive {B : ℕ} (hL : 44 ≤ Real.log B) : 0 < B := by
  apply Nat.pos_of_ne_zero
  intro he
  subst B
  norm_num only [Nat.cast_zero, Real.log_zero] at hL

/-- The winning window lies above the existing finite-thirty-one guard.
Input: a logarithmic endpoint at least forty-four. Claim: its natural endpoint is at least 750.
Proof: compare a contrary endpoint with two to the tenth and use the certified logarithm of two.
Role: preserve the original finite guard in both Jacobi and Selfridge window comparisons. -/
theorem precise_window_input_lower {B : ℕ} (hL : 44 ≤ Real.log B) : 750 ≤ B := by
  by_contra h
  have hs : B ≤ (2 : ℕ) ^ 10 :=
    (Nat.le_of_lt (Nat.lt_of_not_ge h)).trans (by norm_num only : (750 : ℕ) ≤ 2 ^ 10)
  have hsR : (B : ℝ) ≤ (2 : ℝ) ^ 10 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hs
  have hl := Real.log_le_log (Nat.cast_pos.mpr (precise_window_positive hL)) hsR
  rw [Real.log_pow] at hl
  norm_num only at hl
  linarith only [hL, hl, Real.log_two_lt_d9]

/-- Both new radii stay above log squared on every endpoint.
Input: any natural endpoint. Claim: neither majorant is a dedicated non-one improvement.
Proof: split the level logarithm; all corrections are positive away from zero.
Role: compare a later analytic candidate against the complete precise-saving minimum. -/
theorem log_sq_le_preciseRadii (B : ℕ) :
    Real.log B ^ 2 ≤ preciseElementaryRadius B ∧ Real.log B ^ 2 ≤ prime31SavingRadius B := by
  by_cases hB : B = 0
  · subst B
    norm_num only [Nat.cast_zero, Real.log_zero]
    exact ⟨sq_nonneg _, sq_nonneg _⟩
  · have he := precise_level_log_split (Nat.pos_of_ne_zero hB)
    have h0 := Real.log_natCast_nonneg B
    have hq : 1 < Real.log (4 * B : ℕ) := by
      rw [he]
      linarith only [h0, precise_window_log_four.1]
    have hz := Real.log_pos hq
    rw [he] at hz
    have ha : Real.log B ≤ LLS.preciseElementaryRoot (4 * B) := by
      dsimp only [LLS.preciseElementaryRoot]
      rw [he]
      linarith only [h0, hz, precise_window_log_four.1]
    have hb : Real.log B ≤ LLS.prime31SavingRoot (4 * B) := by
      dsimp only [LLS.prime31SavingRoot]
      rw [he]
      linarith only [h0, hz, precise_window_log_four.1]
    exact ⟨(sq_le_sq₀ h0 (h0.trans ha)).mpr ha, (sq_le_sq₀ h0 (h0.trans hb)).mpr hb⟩

/-- A common-scale square includes its nonnegative entrance contribution.
Input: nonnegative coefficient and entrance. Claim: the endpoint maximum covers that entrance.
Proof: square the nonnegative maximum comparison.
Role: the selected Gamma floor comparisons in the complete old minimum. -/
private theorem previous_scale_floor {c E : ℝ} (hc : 0 ≤ c) (hE : 0 ≤ E) (B : ℕ) :
    c * E ^ 2 ≤ logScaleBound c E B := by
  exact
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hE (hE.trans (le_max_left _ _))).mpr (le_max_left _ _)) hc

/-- The retained joint endpoint always exceeds the fixed cap 4093.
Input: any endpoint. Claim: its entrance floor exceeds the cap.
Proof: use the nonnegative scale floor at 255.
Role: reduction of the preceding guarded minimum in the winning window. -/
private theorem previous_joint_floor (B : ℕ) : (4093 : ℝ) ≤ jointEndpointBound B := by
  exact
    (by norm_num only : (4093 : ℝ) ≤ (9999 / 10000 : ℝ) * (255 : ℝ) ^ 2).trans
      (previous_scale_floor (by norm_num only : (0 : ℝ) ≤ 9999 / 10000)
        (by norm_num only : (0 : ℝ) ≤ 255) B)

/-- Both uniform Gamma entrances exceed the retained cap.
Input: any endpoint. Claim: mixed and negative candidates are each at least 4093.
Proof: evaluate their fixed entrance contributions.
Role: check both Gamma branches rather than compare only the old elementary radius. -/
private theorem previous_gamma_floors (B : ℕ) :
    (4093 : ℝ) ≤ mixedScaleBound B ∧ (4093 : ℝ) ≤ negativeScaleBound B := by
  exact
    ⟨(by norm_num only : (4093 : ℝ) ≤ (99 / 100 : ℝ) * (290 : ℝ) ^ 2).trans
        (previous_scale_floor (by norm_num only : (0 : ℝ) ≤ 99 / 100)
          (by norm_num only : (0 : ℝ) ≤ 290) B),
      (by norm_num only : (4093 : ℝ) ≤ (4 / 5 : ℝ) * (46000 : ℝ) ^ 2).trans
        (previous_scale_floor (by norm_num only : (0 : ℝ) ≤ 4 / 5)
          (by norm_num only : (0 : ℝ) ≤ 46000) B)⟩

/-- Every certified old fourth-pole row exceeds the retained cap.
Input: a certified old row and any endpoint. Claim: its fixed entrance already exceeds 4093.
Proof: use the common coefficient and entrance lower bounds.
Role: keep the entire old three-row minimum in the strict comparison. -/
private theorem previous_fourPole_floor (f : LLS.PaperStatements.FourPoleEntry) (B : ℕ) :
    (4093 : ℝ) ≤ fourPoleEntranceBound f B := by
  change 4093 ≤ f.coefficient * max (f.rootEntrance ^ 2) (Real.log B) ^ 2
  have hscale : (100000000 : ℝ) ≤ max (f.rootEntrance ^ 2) (Real.log B) :=
    (LLS.PaperStatements.fourPole_data_scale_lower f).trans (le_max_left _ _)
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 100000000)
          ((by norm_num only : (0 : ℝ) ≤ 100000000).trans hscale)).mpr
      hscale
  have hm :=
    mul_le_mul_of_nonneg_right f.coefficient_lower
      (sq_nonneg (max (f.rootEntrance ^ 2) (Real.log B)))
  nlinarith only [hs, hm]

/-- The complete preceding envelope absorbs the existing small-input witness cap.
Input: an endpoint at least three. Claim: its value is at least thirty-one.
Proof: check every candidate and the guarded two-pole entrance.
Role: transfer the minimum to Selfridge while preserving the original definition. -/
theorem previousEnvelope_ge_thirty_one {B : ℕ} (hB : 3 ≤ B) :
    (31 : ℝ) ≤ previousNegativeEnvelope B := by
  have hj := (by norm_num only : (31 : ℝ) ≤ 4093).trans (previous_joint_floor B)
  have hcap : (31 : ℝ) ≤ if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B := by
    by_cases h : Real.log B ≤ 1609 / 25
    · rw [ite_eq_left h]
      norm_num only
    · rw [ite_eq_right h]
      exact hj
  have hc : (31 : ℝ) ≤ commonEndpointEnvelope B :=
    le_min (refinedRadius_gt_thirtyOne hB).le (le_min hj hcap)
  have hf : (31 : ℝ) ≤ negOneEndpointEnvelope B := by
    apply le_min hc
    by_cases h : B < 750
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact hc
  have hq :
    (31 : ℝ) ≤
      if 500 ≤ Real.log B then quarterClippedTwoPoleNegOneRadius (Real.log B)
      else negOneEndpointEnvelope B := by
    by_cases h : 500 ≤ Real.log B
    · rw [ite_eq_left h]
      have hr :=
        (LLS.quarterClippedNegativeRoot_data
            (by linarith only [h] : (500 : ℝ) ≤ Real.log B + 7 / 5)).1
      have hs :=
        (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 185)
              ((by norm_num only : (0 : ℝ) ≤ 185).trans hr)).mpr
          hr
      exact
        (by norm_num only : (31 : ℝ) ≤ (99 / 40 : ℝ) * (185 : ℝ) ^ 2).trans
          (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 99 / 40))
    · rw [ite_eq_right h]
      exact hf
  have hg := previous_gamma_floors B
  have hk : (4093 : ℝ) ≤ fourPoleReducedBound B :=
    le_min (previous_fourPole_floor _ B)
      (le_min (previous_fourPole_floor _ B) (previous_fourPole_floor _ B))
  exact
    le_min hf
      (le_min ((by norm_num only : (31 : ℝ) ≤ 4093).trans hg.1)
        (le_min ((by norm_num only : (31 : ℝ) ≤ 4093).trans hg.2)
          (le_min ((by norm_num only : (31 : ℝ) ≤ 4093).trans hk) hq)))

/-- The full new envelope still absorbs thirty-one on the nonempty input range.
Input: an endpoint at least three. Claim: the new minimum preserves the small-input floor.
Proof: intersect the preceding floor with the two new radius floors.
Role: sharp Selfridge maximum and trial transfer at nonempty endpoints. -/
theorem preciseEnvelope_ge_thirty_one {B : ℕ} (hB : 3 ≤ B) : (31 : ℝ) ≤ preciseSavingEnvelope B :=
  le_min (previousEnvelope_ge_thirty_one hB)
    (le_min (preciseRadius_gt_thirty_one hB).le
      ((by norm_num only : (31 : ℝ) ≤ 81).trans (prime31Radius_gt_eighty_one hB).le))

/-- Throughout the winning window the complete preceding minimum is exactly 4093.
Input: an endpoint logarithm between forty-four and forty-six.
Claim: no earlier candidate lowers the retained fixed cap.
Proof: preserve all guards and compare the elementary, Gamma and fourth-pole floors.
Role: establish the old whole-minimum value before claiming a strict improvement. -/
theorem previousEnvelope_eq_fixed_cap {B : ℕ} (hL : 44 ≤ Real.log B) (hU : Real.log B ≤ 46) :
    previousNegativeEnvelope B = 4093 := by
  have hBpos := precise_window_positive hL
  have hsplit : Real.log (4 * (B : ℝ)) = Real.log B + Real.log 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using precise_level_log_split hBpos
  have hr : (65 : ℝ) < refinedElementaryRoot B := by
    dsimp only [refinedElementaryRoot]
    rw [hsplit]
    exact precise_window_refined_gt hL
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 65)
          ((by norm_num only : (0 : ℝ) ≤ 65).trans hr.le)).mpr
      hr
  have he : (4093 : ℝ) ≤ refinedElementaryRadius B :=
    (by norm_num only : (4093 : ℝ) ≤ (65 : ℝ) ^ 2).trans hs.le
  have hcap : Real.log B ≤ 1609 / 25 := hU.trans (by norm_num only : (46 : ℝ) ≤ 1609 / 25)
  have hc : commonEndpointEnvelope B = 4093 := by
    change
      min (refinedElementaryRadius B)
          (min (jointEndpointBound B)
            (if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B)) =
        4093
    rw [ite_eq_left hcap, min_eq_right (previous_joint_floor B), min_eq_right he]
  have hf : negOneEndpointEnvelope B = 4093 := by
    change min (commonEndpointEnvelope B) (if B < 750 then 31 else commonEndpointEnvelope B) = 4093
    rw [ite_eq_right (Nat.not_lt.mpr (precise_window_input_lower hL)), min_self, hc]
  have hq : ¬500 ≤ Real.log B := by linarith only [hU]
  have hg := previous_gamma_floors B
  have hk : (4093 : ℝ) ≤ fourPoleReducedBound B :=
    le_min (previous_fourPole_floor _ B)
      (le_min (previous_fourPole_floor _ B) (previous_fourPole_floor _ B))
  change
    min (negOneEndpointEnvelope B)
        (min (mixedScaleBound B)
          (min (negativeScaleBound B)
            (min (fourPoleReducedBound B)
              (if 500 ≤ Real.log B then quarterClippedTwoPoleNegOneRadius (Real.log B)
              else negOneEndpointEnvelope B)))) =
      4093
  rw [ite_eq_right hq, hf, min_eq_right hk, min_eq_right hg.2, min_eq_right hg.1, min_self]

/-- The cutoff-thirty-one radius is below 3969 throughout the continuous winning window.
Input: the same logarithmic interval. Claim: the new radius is below sixty-three squared.
Proof: split the original-level logarithm and square the positive certified root comparison.
Role: the new side of the complete public-minimum comparison. -/
theorem prime31Radius_lt_window {B : ℕ} (hL : 44 ≤ Real.log B) (hU : Real.log B ≤ 46) :
    prime31SavingRadius B < 3969 := by
  have hb := precise_window_prime31_bounds hL hU
  have he :
    LLS.prime31SavingRoot (4 * B) =
      (33 / 31 : ℝ) * (Real.log B + Real.log 4) + (4 / 5 : ℝ) * Real.log (Real.log B + Real.log 4) +
        18327 / 2000 := by
    dsimp only [LLS.prime31SavingRoot]
    rw [precise_level_log_split (precise_window_positive hL)]
  have hs :=
    (sq_lt_sq₀ ((by norm_num only : (0 : ℝ) ≤ 9).trans hb.1.le)
          (by norm_num only : (0 : ℝ) ≤ 63)).mpr
      hb.2
  change LLS.prime31SavingRoot (4 * B) ^ 2 < 3969
  rw [he]
  norm_num only at hs
  exact hs

/-- The full precise-saving envelope strictly improves the complete preceding public minimum.
Input: an endpoint logarithm between forty-four and forty-six.
Claim: the new all-candidate minimum is strictly smaller than the old one.
Proof: select R31 below 3969 while the full preceding minimum equals 4093.
Role: a continuous winning interval, rather than a finite collection of displayed bit widths. -/
theorem preciseSavingEnvelope_strict_window {B : ℕ} (hL : 44 ≤ Real.log B) (hU : Real.log B ≤ 46) :
    preciseSavingEnvelope B < previousNegativeEnvelope B :=
  (preciseSavingEnvelope_le_prime31 B).trans_lt
    ((prime31Radius_lt_window hL hU).trans
      ((by norm_num only : (3969 : ℝ) < 4093).trans_eq (previousEnvelope_eq_fixed_cap hL hU).symm))

end PseudoPrime.PseudoSquare
