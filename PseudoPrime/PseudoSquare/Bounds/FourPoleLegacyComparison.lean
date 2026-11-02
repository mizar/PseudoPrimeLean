/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FourPoleReducedBounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPolePrefixBounds
public import PseudoPrime.PseudoSquare.Bounds.QuarterLogClippedNegOneBounds
public import PseudoPrime.PseudoSquare.Bounds.CommonEndpointBounds

/-! # Comparison with the former complete high-domain candidate minima

The former plotting scripts expose both regime-selected bounds and direct candidate
arrays. Above logarithmic scale nine hundred million, their finite and bounded-interval
guards are inactive. The tails below retain every other direct candidate; the joint
endpoint candidate equals the repeated coefficient-9999/10000 branch in this domain.
Thus no earlier shifted or logarithmic candidate is dropped merely because a later
regime is selected. These comparison models are used only in their stated high domain.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The remaining active direct non-one candidates in the former high-domain model.
Input: an endpoint. Output: the minimum of all branches other than four fifths and U4.
Role: check earlier shifted candidates as well as the selected high-domain regime. -/
noncomputable def legacyNeOneTail (B : ℕ) : ℝ :=
  let L := Real.log B
  min (L ^ 2)
    (min ((L - 1 / 1000) ^ 2)
      (min ((L - 1 / 10) ^ 2)
        (min ((L - 1 / 2) ^ 2)
          (min ((L - Real.log L + 3) ^ 2)
            (min ((L - Real.log L + 11 / 4) ^ 2)
              (min ((L - 2 * Real.log L + 37 / 5) ^ 2)
                (min (eulerPrefixTwoPoleNeOneRadius L)
                  (min ((99 / 100 : ℝ) * L ^ 2) (jointEndpointBound B)))))))))

/-- The remaining active direct negative candidates in the former high-domain model.
Input: an endpoint. Output: the elementary, clipped two-pole, mixed and joint minimum.
Role: retain the unconditional elementary branch in the complete former candidate set. -/
noncomputable def legacyNegOneTail (B : ℕ) : ℝ :=
  let L := Real.log B
  min ((L + Real.log 4 + (24 / 5 : ℝ) * Real.log (L + Real.log 4) + 3) ^ 2)
    (min (quarterClippedTwoPoleNegOneRadius L)
      (min ((99 / 100 : ℝ) * L ^ 2) (jointEndpointBound B)))

/-- The complete former non-one candidate minimum in the high logarithmic domain.
Input: an endpoint. Output: the old direct minimum, with inactive finite guards removed.
Role: compare the reduced entrance against all formerly available branches at once. -/
noncomputable def legacyHighNeOneBound (B : ℕ) : ℝ :=
  min ((4 / 5 : ℝ) * Real.log B ^ 2) (min (fourPoleCumulativeBound B) (legacyNeOneTail B))

/-- The complete former negative candidate minimum in the high logarithmic domain.
Input: an endpoint. Output: the old direct minimum after removing inactive finite guards.
Role: compare both witness maxima against their separate former candidate sets. -/
noncomputable def legacyHighNegOneBound (B : ℕ) : ℝ :=
  min ((4 / 5 : ℝ) * Real.log B ^ 2) (min (fourPoleCumulativeBound B) (legacyNegOneTail B))

/-- A root above 98 percent of a nonnegative scale has square at least four fifths of its square.
Input: a nonnegative scale and a covering root. Claim: the squared lower bound.
Proof: square the root comparison. Role: all earlier shifted and logarithmic candidates. -/
private theorem legacy_square_floor {L r : ℝ} (hL : 0 ≤ L) (hr : (49 / 50 : ℝ) * L ≤ r) :
    (4 / 5 : ℝ) * L ^ 2 ≤ r ^ 2 := by
  have h0 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 49 / 50) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- A root above the two-pole linear term gives a radius above four fifths.
Input: a nonnegative scale and a covering root. Claim: the two-pole squared-radius floor.
Proof: square and compare exact rational coefficients. Role: both former two-pole branches. -/
private theorem legacy_twoPole_floor {L r : ℝ} (hL : 0 ≤ L) (hr : (500 / 821 : ℝ) * L ≤ r) :
    (4 / 5 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * r ^ 2 := by
  have h0 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 500 / 821) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- In the comparison domain the logarithm is at most one percent of the scale.
Input: a scale at least nine hundred million. Claim: the logarithmic allowance.
Proof: combine the established square-root cap with square root at most the scale.
Role: check every former single-log and double-log direct candidate. -/
private theorem legacy_log_cap {L : ℝ} (hL : 900000000 ≤ L) : Real.log L ≤ L / 100 := by
  have hb :=
    LLS.PaperStatements.fourPole_log_le_sqrt
      ((by norm_num only : (100000000 : ℝ) ≤ 900000000).trans hL)
  have hs := Real.sqrt_le_self_iff.mpr (Or.inr ((by norm_num only : (1 : ℝ) ≤ 900000000).trans hL))
  linarith only [hb, hs]

/-- All earlier direct non-one candidates exceed the four-fifths branch in the high domain.
Input: a sufficiently large endpoint logarithm. Claim: no tail candidate lowers that branch.
Proof: explicit shifted-root floors and the two-pole leading coefficient.
Role: validate the complete direct-array minimum rather than a selected scalar branch. -/
private theorem legacy_neOne_tail_floor {B : ℕ} (hL : 900000000 ≤ Real.log B) :
    (4 / 5 : ℝ) * Real.log B ^ 2 ≤ legacyNeOneTail B := by
  have h0 := Real.log_natCast_nonneg B
  have hl := legacy_log_cap hL
  have h1 :=
    legacy_square_floor h0 (by linarith only [h0] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B)
  have h2 :=
    legacy_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 1000)
  have h3 :=
    legacy_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 10)
  have h4 :=
    legacy_square_floor h0 (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 2)
  have h5 :=
    legacy_square_floor h0
      (by linarith only [hl, h0] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - Real.log (Real.log B) + 3)
  have h6 :=
    legacy_square_floor h0
      (by linarith only [hl, h0] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - Real.log (Real.log B) + 11 / 4)
  have h7 :=
    legacy_square_floor h0
      (by linarith only [hl] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 2 * Real.log (Real.log B) + 37 / 5)
  have hp : (4 / 5 : ℝ) * Real.log B ^ 2 ≤ eulerPrefixTwoPoleNeOneRadius (Real.log B) :=
    legacy_twoPole_floor h0 (by linarith only)
  have hm :=
    mul_le_mul_of_nonneg_right (by norm_num only : (4 / 5 : ℝ) ≤ 99 / 100) (sq_nonneg (Real.log B))
  have hj : (4 / 5 : ℝ) * Real.log B ^ 2 ≤ jointEndpointBound B := by
    change (4 / 5 : ℝ) * Real.log B ^ 2 ≤ (9999 / 10000 : ℝ) * max 255 (Real.log B) ^ 2
    rw [max_eq_right ((by norm_num only : (255 : ℝ) ≤ 900000000).trans hL)]
    exact mul_le_mul_of_nonneg_right (by norm_num only : (4 / 5 : ℝ) ≤ 9999 / 10000) (sq_nonneg _)
  exact
    le_min h1
      (le_min h2
        (le_min h3 (le_min h4 (le_min h5 (le_min h6 (le_min h7 (le_min hp (le_min hm hj))))))))

/-- All earlier direct negative candidates exceed four fifths in the high domain.
Input: a sufficiently large endpoint logarithm. Claim: elementary and two-pole tails are larger.
Proof: positivity of the elementary corrections and the two-pole leading coefficient.
Role: validate the separate former negative-witness candidate minimum. -/
private theorem legacy_negOne_tail_floor {B : ℕ} (hL : 900000000 ≤ Real.log B) :
    (4 / 5 : ℝ) * Real.log B ^ 2 ≤ legacyNegOneTail B := by
  have h0 := Real.log_natCast_nonneg B
  have h4 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
  have hlevel : 1 ≤ Real.log B + Real.log 4 := by linarith only [hL, h4]
  have hl := Real.log_nonneg hlevel
  have he :=
    legacy_square_floor h0
      (by linarith only [h0, h4, hl] :
        (49 / 50 : ℝ) * Real.log B ≤
          Real.log B + Real.log 4 + (24 / 5 : ℝ) * Real.log (Real.log B + Real.log 4) + 3)
  have hlp := Real.log_nonneg (by linarith only [hL] : (1 : ℝ) ≤ Real.log B + 7 / 5)
  have hp : (4 / 5 : ℝ) * Real.log B ^ 2 ≤ quarterClippedTwoPoleNegOneRadius (Real.log B) :=
    legacy_twoPole_floor h0
      (by
        dsimp only [LLS.quarterClippedNegativeRoot]
        linarith only [hlp])
  have hm :=
    mul_le_mul_of_nonneg_right (by norm_num only : (4 / 5 : ℝ) ≤ 99 / 100) (sq_nonneg (Real.log B))
  have hj : (4 / 5 : ℝ) * Real.log B ^ 2 ≤ jointEndpointBound B := by
    change (4 / 5 : ℝ) * Real.log B ^ 2 ≤ (9999 / 10000 : ℝ) * max 255 (Real.log B) ^ 2
    rw [max_eq_right ((by norm_num only : (255 : ℝ) ≤ 900000000).trans hL)]
    exact mul_le_mul_of_nonneg_right (by norm_num only : (4 / 5 : ℝ) ≤ 9999 / 10000) (sq_nonneg _)
  exact le_min he (le_min hp (le_min hm hj))

/-- The old complete non-one minimum reduces to four fifths and the former U4 branch.
Input: a high-domain endpoint. Claim: every other active direct candidate is redundant.
Proof: use the complete tail lower bound. Role: exact comparison with the former public minimum. -/
theorem legacyHighNeOne_eq {B : ℕ} (hL : 900000000 ≤ Real.log B) :
    legacyHighNeOneBound B = min ((4 / 5 : ℝ) * Real.log B ^ 2) (fourPoleCumulativeBound B) := by
  change
    min ((4 / 5 : ℝ) * Real.log B ^ 2) (min (fourPoleCumulativeBound B) (legacyNeOneTail B)) = _
  rw [← min_assoc]
  exact min_eq_left ((min_le_left _ _).trans (legacy_neOne_tail_floor hL))

/-- The old complete negative minimum has the same two high-domain candidates.
Input: a high-domain endpoint. Claim: the elementary and two-pole tails do not lower the minimum.
Proof: use the complete negative tail lower bound. Role: compare the former negative minimum. -/
theorem legacyHighNegOne_eq {B : ℕ} (hL : 900000000 ≤ Real.log B) :
    legacyHighNegOneBound B = min ((4 / 5 : ℝ) * Real.log B ^ 2) (fourPoleCumulativeBound B) := by
  change
    min ((4 / 5 : ℝ) * Real.log B ^ 2) (min (fourPoleCumulativeBound B) (legacyNegOneTail B)) = _
  rw [← min_assoc]
  exact min_eq_left ((min_le_left _ _).trans (legacy_negOne_tail_floor hL))

/-- Up to logarithmic scale one quadrillion, the former U4 branch exceeds four fifths.
Input: a nonnegative endpoint logarithm no larger than that scale. Claim: the U4 floor.
Proof: compare the squared endpoint with the fixed history constant.
Role: identify the complete former minimum over the reduced-entrance winning interval. -/
private theorem legacy_fourPole_floor {B : ℕ} (hU : Real.log B ≤ (10 : ℝ) ^ 15) :
    (4 / 5 : ℝ) * Real.log B ^ 2 ≤ fourPoleCumulativeBound B := by
  have hs :=
    (sq_le_sq₀ (Real.log_natCast_nonneg B) (by norm_num only : (0 : ℝ) ≤ (10 : ℝ) ^ 15)).mpr hU
  exact
    ((mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 4 / 5)).trans
          (by norm_num only :
            (4 / 5 : ℝ) * ((10 : ℝ) ^ 15) ^ 2 ≤ (9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2)).trans
      (le_max_left _ _)

/-- The reduced entrance strictly beats both complete former high-domain candidate minima.
Input: an endpoint logarithm between nine hundred million and one quadrillion.
Claim: the reduced bound improves both formerly published candidate sets.
Proof: the former minima equal four fifths times log squared throughout this interval.
Role: a certified strict winning interval for Q3, including every earlier direct branch. -/
theorem fourPole_reduced_lt_old_min {B : ℕ} (hL : 900000000 ≤ Real.log B)
    (hU : Real.log B ≤ (10 : ℝ) ^ 15) :
    fourPoleReducedBound B < legacyHighNeOneBound B ∧
      fourPoleReducedBound B < legacyHighNegOneBound B := by
  rw [legacyHighNeOne_eq hL, legacyHighNegOne_eq hL, min_eq_left (legacy_fourPole_floor hU)]
  exact ⟨fourPole_reduced_lt_smoothed hL, fourPole_reduced_lt_smoothed hL⟩

/-- The common-scale Q2 bound also strictly improves both complete former minima.
Input: an endpoint logarithm between the old entrance and eleven tenths of it.
Claim: the common-scale bound improves both old candidate sets.
Proof: it lies below both four fifths and the old history branch.
Role: retain a strict Q2 comparison independently of the later reduced entrances. -/
theorem fourPole_common_lt_old_min {B : ℕ} (hL : (10 : ℝ) ^ 18 ≤ Real.log B)
    (hU : Real.log B ≤ (11 / 10 : ℝ) * (10 : ℝ) ^ 18) :
    fourPoleScaleBound B < legacyHighNeOneBound B ∧
      fourPoleScaleBound B < legacyHighNegOneBound B := by
  have hbase := (by norm_num only : (900000000 : ℝ) ≤ (10 : ℝ) ^ 18).trans hL
  rw [legacyHighNeOne_eq hbase, legacyHighNegOne_eq hbase]
  have hs : fourPoleScaleBound B < (4 / 5 : ℝ) * Real.log B ^ 2 := by
    change (777 / 1000 : ℝ) * max ((10 : ℝ) ^ 18) (Real.log B) ^ 2 < (4 / 5 : ℝ) * Real.log B ^ 2
    rw [max_eq_right hL]
    exact
      mul_lt_mul_of_pos_right (by norm_num only : (777 / 1000 : ℝ) < 4 / 5)
        (sq_pos_of_pos ((by norm_num only : (0 : ℝ) < (10 : ℝ) ^ 18).trans_le hL))
  exact ⟨lt_min hs (fourPole_scale_lt_legacy hL hU), lt_min hs (fourPole_scale_lt_legacy hL hU)⟩

end PseudoPrime.PseudoSquare
