/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.GammaCommonBounds
public import PseudoPrime.PseudoSquare.Bounds.FourPoleLegacyComparison
public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
public import PseudoPrime.LLS.QuadraticGammaSmoothedNumerics

/-! # Whole-minimum winning intervals for the three common-scale Gamma candidates

These comparison models retain all active branches from the former plotting scripts.
The mixed window is negative-only: earlier non-one double-logarithm estimates are
already smaller there. The two later windows reuse the complete direct-candidate tails,
but omit the four-fifths branch before its respective entrance. Finite caps and the
bounded Euler window are inactive throughout these intervals. No witness theorem or
arithmetic hypothesis is changed; all statements below compare certified candidate values.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The former complete negative minimum in the window just below scale 290.
Input: an endpoint. Output: the elementary, joint and former fourth-pole minimum.
Role: compare the mixed candidate before the mixed pointwise branch becomes active. -/
noncomputable def legacyMixedWindowBound (B : ℕ) : ℝ :=
  let L := Real.log B
  min ((L + Real.log 4 + (24 / 5 : ℝ) * Real.log (L + Real.log 4) + 3) ^ 2)
    (min (jointEndpointBound B) (fourPoleCumulativeBound B))

/-- The former complete non-one minimum before its four-fifths entrance.
Input: an endpoint. Output: all earlier active direct branches and the former U4 value.
Role: certify an actual whole-minimum improvement before logarithmic scale 22221. -/
noncomputable def legacyNeOneWindowBound (B : ℕ) : ℝ :=
  min (legacyNeOneTail B) (fourPoleCumulativeBound B)

/-- The former complete negative minimum before its decimal four-fifths entrance.
Input: an endpoint. Output: every earlier active negative branch and the former U4 value.
Role: certify the negative common-scale improvement without a non-one branch. -/
noncomputable def legacyNegOneWindowBound (B : ℕ) : ℝ :=
  min (legacyNegOneTail B) (fourPoleCumulativeBound B)

/-- On scales at least ten thousand, the logarithm uses at most one percent of the scale.
Input: the lower scale bound. Claim: a uniform logarithmic cap.
Proof: use the existing square-root bound and square the linear comparison.
Role: all shifted and logarithmic direct-candidate lower bounds in these windows. -/
private theorem gamma_window_log_cap {L : ℝ} (hL : 10000 ≤ L) : Real.log L ≤ L / 100 := by
  have h0 := (by norm_num only : (0 : ℝ) ≤ 10000).trans hL
  have hm := mul_le_mul_of_nonneg_right hL h0
  have hs : Real.sqrt L ≤ L / 100 :=
    Real.sqrt_le_iff.mpr ⟨div_nonneg h0 (by norm_num only : (0 : ℝ) ≤ 100), by nlinarith only [hm]⟩
  exact (Analysis.log_le_sqrt_of_pos ((by norm_num only : (0 : ℝ) < 10000).trans_le hL)).trans hs

/-- A root above 98 percent of a nonnegative scale has square above nine tenths.
Input: a scale and a lower root comparison. Claim: the squared floor.
Proof: square and compare rational coefficients. Role: earlier direct non-one candidates. -/
private theorem gamma_window_square_floor {L r : ℝ} (hL : 0 ≤ L) (hr : (49 / 50 : ℝ) * L ≤ r) :
    (9 / 10 : ℝ) * L ^ 2 ≤ r ^ 2 := by
  have h0 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 49 / 50) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- Either two-pole leading term has coefficient above nine tenths after squaring.
Input: a nonnegative scale and root covering its linear term. Claim: the radius floor.
Proof: exact rational squared comparison. Role: both former two-pole branches. -/
private theorem gamma_window_twoPole_floor {L r : ℝ} (hL : 0 ≤ L) (hr : (500 / 821 : ℝ) * L ≤ r) :
    (9 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * r ^ 2 := by
  have h0 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 500 / 821) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- The elementary direct radius covers the squared logarithmic scale.
Input: a scale at least one. Claim: its positive corrections only enlarge the root.
Proof: positivity of both logarithmic corrections. Role: mixed and negative old minima. -/
private theorem gamma_window_elementary_floor {L : ℝ} (hL : 1 ≤ L) :
    L ^ 2 ≤ (L + Real.log 4 + (24 / 5 : ℝ) * Real.log (L + Real.log 4) + 3) ^ 2 := by
  have h0 := (by norm_num only : (0 : ℝ) ≤ 1).trans hL
  have h4 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
  have hl := Real.log_nonneg (show 1 ≤ L + Real.log 4 by linarith only [hL, h4])
  exact (sq_le_sq₀ h0 (by linarith only [h0, h4, hl])).mpr (by linarith only [h4, hl])

/-- The joint endpoint branch exceeds nine tenths of log squared in both later windows.
Input: a logarithmic endpoint at least 255. Claim: the joint branch floor.
Proof: select the endpoint maximum and compare coefficients.
Role: retain the joint candidate in each complete former minimum. -/
private theorem gamma_window_joint_floor {B : ℕ} (hL : 255 ≤ Real.log B) :
    (9 / 10 : ℝ) * Real.log B ^ 2 ≤ jointEndpointBound B := by
  change (9 / 10 : ℝ) * Real.log B ^ 2 ≤ (9999 / 10000 : ℝ) * max 255 (Real.log B) ^ 2
  rw [max_eq_right hL]
  exact mul_le_mul_of_nonneg_right (by norm_num only : (9 / 10 : ℝ) ≤ 9999 / 10000) (sq_nonneg _)

/-- The old fourth-pole history is above nine tenths throughout the two later windows.
Input: an endpoint logarithm at most 45000. Claim: the history floor.
Proof: square the endpoint bound and compare its exact fixed contribution.
Role: include U4 rather than silently discard it from the old minima. -/
private theorem gamma_window_history_floor {B : ℕ} (hU : Real.log B ≤ 45000) :
    (9 / 10 : ℝ) * Real.log B ^ 2 ≤ fourPoleCumulativeBound B := by
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg B) (by norm_num only : (0 : ℝ) ≤ 45000)).mpr hU
  exact
    ((mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 9 / 10)).trans
          (by norm_num only :
            (9 / 10 : ℝ) * (45000 : ℝ) ^ 2 ≤ (9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2)).trans
      (le_max_left _ _)

/-- Every active direct non-one branch exceeds nine tenths after logarithmic scale 21000.
Input: that lower endpoint. Claim: the complete earlier tail has the stated floor.
Proof: bound logarithmic corrections and check the two-pole leading coefficient.
Role: a whole-minimum lower certificate for the dedicated non-one Gamma candidate. -/
private theorem gamma_window_neOne_floor {B : ℕ} (hL : 21000 ≤ Real.log B) :
    (9 / 10 : ℝ) * Real.log B ^ 2 ≤ legacyNeOneTail B := by
  have h0 := Real.log_natCast_nonneg B
  have hl := gamma_window_log_cap ((by norm_num only : (10000 : ℝ) ≤ 21000).trans hL)
  have h1 :=
    gamma_window_square_floor h0 (by linarith only [h0] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B)
  have h2 :=
    gamma_window_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 1000)
  have h3 :=
    gamma_window_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 10)
  have h4 :=
    gamma_window_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 2)
  have h5 :=
    gamma_window_square_floor h0
      (by linarith only [hl, h0] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - Real.log (Real.log B) + 3)
  have h6 :=
    gamma_window_square_floor h0
      (by linarith only [hl, h0] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - Real.log (Real.log B) + 11 / 4)
  have h7 :=
    gamma_window_square_floor h0
      (by linarith only [hl] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 2 * Real.log (Real.log B) + 37 / 5)
  have hp : (9 / 10 : ℝ) * Real.log B ^ 2 ≤ eulerPrefixTwoPoleNeOneRadius (Real.log B) :=
    gamma_window_twoPole_floor h0 (by linarith only)
  have hm :=
    mul_le_mul_of_nonneg_right (by norm_num only : (9 / 10 : ℝ) ≤ 99 / 100) (sq_nonneg (Real.log B))
  have hj : (9 / 10 : ℝ) * Real.log B ^ 2 ≤ jointEndpointBound B := by
    change (9 / 10 : ℝ) * Real.log B ^ 2 ≤ (9999 / 10000 : ℝ) * max 255 (Real.log B) ^ 2
    rw [max_eq_right ((by norm_num only : (255 : ℝ) ≤ 21000).trans hL)]
    exact mul_le_mul_of_nonneg_right (by norm_num only : (9 / 10 : ℝ) ≤ 9999 / 10000) (sq_nonneg _)
  exact
    le_min h1
      (le_min h2
        (le_min h3 (le_min h4 (le_min h5 (le_min h6 (le_min h7 (le_min hp (le_min hm hj))))))))

/-- Every earlier direct negative branch exceeds nine tenths after logarithmic scale 44000.
Input: that lower endpoint. Claim: the complete earlier negative tail has the stated floor.
Proof: the elementary and clipped two-pole comparisons and exact mixed coefficient.
Role: a whole-minimum certificate with negative-witness semantics preserved. -/
private theorem gamma_window_negOne_floor {B : ℕ} (hL : 44000 ≤ Real.log B) :
    (9 / 10 : ℝ) * Real.log B ^ 2 ≤ legacyNegOneTail B := by
  have h0 := Real.log_natCast_nonneg B
  have hsmall : (9 / 10 : ℝ) * Real.log B ^ 2 ≤ Real.log B ^ 2 := by
    nlinarith only [sq_nonneg (Real.log B)]
  have he :=
    hsmall.trans (gamma_window_elementary_floor ((by norm_num only : (1 : ℝ) ≤ 44000).trans hL))
  have hl := Real.log_nonneg (by linarith only [hL] : (1 : ℝ) ≤ Real.log B + 7 / 5)
  have hp : (9 / 10 : ℝ) * Real.log B ^ 2 ≤ quarterClippedTwoPoleNegOneRadius (Real.log B) :=
    gamma_window_twoPole_floor h0
      (by
        dsimp only [LLS.quarterClippedNegativeRoot]
        linarith only [hl])
  have hm :=
    mul_le_mul_of_nonneg_right (by norm_num only : (9 / 10 : ℝ) ≤ 99 / 100) (sq_nonneg (Real.log B))
  exact
    le_min he
      (le_min hp
        (le_min hm (gamma_window_joint_floor ((by norm_num only : (255 : ℝ) ≤ 44000).trans hL))))

/-- The negative window ends before the old decimal four-fifths branch is available.
Input: an endpoint logarithm at most 45000. Claim: it is below 19978 log 10.
Proof: use the established rational lower bound for log ten.
Role: justify the inactive Gamma guard in the complete former negative minimum. -/
theorem negative_window_before_decimal {B : ℕ} (hU : Real.log B ≤ 45000) :
    Real.log B < (19978 : ℝ) * Real.log 10 := by
  linarith only [hU, LLS.log_ten_gt_twenty_three_tenths]

/-- The mixed common-scale candidate strictly improves the complete former negative minimum.
Input: an endpoint logarithm between 289 and 289.5. Claim: all earlier active branches lose.
Proof: compare with the elementary, joint and old history candidates separately.
Role: certify a continuous winning interval without claiming a non-one improvement. -/
theorem mixed_scale_lt_old_min {B : ℕ} (hL : 289 ≤ Real.log B) (hU : Real.log B ≤ (579 / 2 : ℝ)) :
    mixedScaleBound B < legacyMixedWindowBound B := by
  have hu : Real.log B ≤ 290 := hU.trans (by norm_num only : (579 / 2 : ℝ) ≤ 290)
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 289) (Real.log_natCast_nonneg B)).mpr hL
  have he : mixedScaleBound B < Real.log B ^ 2 := by
    change (99 / 100 : ℝ) * max 290 (Real.log B) ^ 2 < Real.log B ^ 2
    rw [max_eq_left hu]
    nlinarith only [hs]
  have hh : mixedScaleBound B < fourPoleCumulativeBound B := by
    change (99 / 100 : ℝ) * max 290 (Real.log B) ^ 2 < _
    rw [max_eq_left hu]
    exact
      (by norm_num only :
            (99 / 100 : ℝ) * (290 : ℝ) ^ 2 < (9999 / 10000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2).trans_le
        (le_max_left _ _)
  exact
    lt_min
      (he.trans_le (gamma_window_elementary_floor ((by norm_num only : (1 : ℝ) ≤ 289).trans hL)))
      (lt_min (mixed_scale_lt_joint hL hu) hh)

/-- The dedicated non-one common-scale candidate strictly beats the complete former minimum.
Input: an endpoint logarithm between 21000 and 22000. Claim: every old active candidate is larger.
Proof: all old branches exceed nine tenths of log squared, while the new fixed row is smaller.
Role: certify the second Gamma candidate's actual continuous winning interval. -/
theorem neOne_scale_lt_old_min {B : ℕ} (hL : 21000 ≤ Real.log B) (hU : Real.log B ≤ 22000) :
    neOneScaleBound B < legacyNeOneWindowBound B := by
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 21000) (Real.log_natCast_nonneg B)).mpr hL
  have hb : neOneScaleBound B < (9 / 10 : ℝ) * Real.log B ^ 2 := by
    change (4 / 5 : ℝ) * max 22221 (Real.log B) ^ 2 < (9 / 10 : ℝ) * Real.log B ^ 2
    rw [max_eq_left (hU.trans (by norm_num only : (22000 : ℝ) ≤ 22221))]
    nlinarith only [hs]
  exact
    hb.trans_le
      (le_min (gamma_window_neOne_floor hL)
        (gamma_window_history_floor (hU.trans (by norm_num only : (22000 : ℝ) ≤ 45000))))

/-- The negative common-scale candidate strictly beats the complete former negative minimum.
Input: an endpoint logarithm between 44000 and 45000. Claim: every old active negative branch loses.
Proof: compare the new fixed row with the complete nine-tenths lower certificate.
Role: certify the third Gamma candidate without importing the dedicated non-one bound. -/
theorem negative_scale_lt_old_min {B : ℕ} (hL : 44000 ≤ Real.log B) (hU : Real.log B ≤ 45000) :
    negativeScaleBound B < legacyNegOneWindowBound B := by
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 44000) (Real.log_natCast_nonneg B)).mpr hL
  have hb : negativeScaleBound B < (9 / 10 : ℝ) * Real.log B ^ 2 := by
    change (4 / 5 : ℝ) * max 46000 (Real.log B) ^ 2 < (9 / 10 : ℝ) * Real.log B ^ 2
    rw [max_eq_left (hU.trans (by norm_num only : (45000 : ℝ) ≤ 46000))]
    nlinarith only [hs]
  exact hb.trans_le (le_min (gamma_window_negOne_floor hL) (gamma_window_history_floor hU))

end PseudoPrime.PseudoSquare
