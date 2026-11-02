/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FourPoleAbelBounds
public import PseudoPrime.PseudoSquare.Bounds.PreciseSavingEnvelope
public import PseudoPrime.PseudoSquare.QNeOneRetainedReciprocalAnalytic
public import PseudoPrime.PseudoSquare.QNeOneDeciShiftBounds
public import PseudoPrime.PseudoSquare.QNeOneHalfShiftBounds
public import PseudoPrime.PseudoSquare.QNeOneLogShiftBounds
public import PseudoPrime.PseudoSquare.Bounds.ElevenFourthsFromNinetySix
public import PseudoPrime.PseudoSquare.Bounds.FiniteScaleShiftedDoubleLogBounds
public import PseudoPrime.PseudoSquare.Bounds.TwoPolePrefixBounds
public import PseudoPrime.PseudoSquare.Bounds.OddMidscaleEndpointBounds
public import PseudoPrime.PseudoSquare.Bounds.FourPoleLegacyComparison
public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # The full non-one baseline and the new double-Abel minima

All preceding direct guards and shared candidates remain in the baseline.
Fixed K4 row selection and winning-window certificates belong to this comparison leaf.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- The complete preceding non-one minimum at a natural endpoint.
It retains the five small-input cap, every shifted-log guard, the finite forty-seven
cap and bounded midscale window. The shared fallback includes the complete negative
Q5 envelope and the dedicated four-fifths candidate. Below three the maximum is zero.
Role: compare all preceding candidates without discarding dedicated non-one estimates. -/
noncomputable def previousNonOneEnvelope (B : ℕ) : ℝ :=
  if B < 3 then 0
  else
    let L := Real.log B
    let C := min (preciseSavingEnvelope B) (neOneScaleBound B)
    min (if B < 10 then 5 else L ^ 2)
      (min (if 2984 ≤ B then (L - 1 / 1000) ^ 2 else C)
        (min (if 3295 ≤ B then (L - 1 / 10) ^ 2 else C)
          (min (if (25 / 2 : ℝ) ≤ L then (L - 1 / 2) ^ 2 else C)
            (min (if (16 : ℝ) ≤ L then (L - Real.log L + 3) ^ 2 else C)
              (min (if (96 : ℝ) ≤ L then (L - Real.log L + 11 / 4) ^ 2 else C)
                (min (if (50 : ℝ) ≤ L then (L - 2 * Real.log L + 37 / 5) ^ 2 else C)
                  (min (if (500 : ℝ) ≤ L then eulerPrefixTwoPoleNeOneRadius L else C)
                    (min (if B < 1000000 then 47 else C)
                      (min
                        (if (3259 / 25 : ℝ) ≤ L ∧ L ≤ 16277 / 100 then
                          (LLS.PaperStatements.oddMidscaleEndpointRadius L) ^ 2
                        else C)
                        (C))))))))))

/-- Intersect the preceding precise-saving negative minimum with the new Abel rows.
Input: any natural endpoint. Output: the selected cumulative negative radius.
Role: preserve every old candidate while adding the improved analytic entrances. -/
noncomputable def fourPoleAbelNegEnvelope (B : ℕ) : ℝ :=
  min (preciseSavingEnvelope B) (fourPoleAbelBound B)

/-- Intersect the complete preceding non-one minimum with the new Abel rows.
Input: any natural endpoint. Output: the selected cumulative non-one radius.
Role: retain dedicated factor-detecting improvements alongside the new negative bound. -/
noncomputable def fourPoleAbelNeEnvelope (B : ℕ) : ℝ :=
  min (previousNonOneEnvelope B) (fourPoleAbelBound B)

/-- A positive endpoint logarithm implies a positive natural endpoint.
Exclude zero using log zero. This discharges the domain of guarded logarithmic APIs. -/
private theorem previous_positive_of_log {B : ℕ} (hL : 0 < Real.log B) : 0 < B := by
  by_cases hz : B = 0
  · subst B
    norm_num only [Nat.cast_zero, Real.log_zero] at hL
  · exact Nat.pos_of_ne_zero hz

/-- Below endpoint ten, every admissible input has non-one witness at most five.
Use the existing finite certificate below sixteen and lift it to the maximum.
Role: preserve the small-input candidate in the complete preceding model. -/
private theorem previous_nonOne_small {B : ℕ} (hB : B < 10) : (QNeOne B : ℝ) ≤ 5 := by
  apply QNeOne_cast_le_of_forall (by norm_num only : (0 : ℝ) ≤ 5)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn16 : n < 16 := (lt_of_le_of_lt ha.le hB).trans (by norm_num only : (10 : ℕ) < 16)
  exact Nat.cast_le.mpr (primeNeOneWitness_le_five_of_lt_sixteen ha.odd ha.not_isSquare hn16)

/-- Under GRH, the complete preceding non-one minimum bounds its actual maximum.
Apply every certified branch under its original guard and intersect the results.
The empty input domain uses its exact zero maximum. Role: validate the full baseline. -/
theorem QNeOne_le_previousNonOne (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ previousNonOneEnvelope B := by
  by_cases hsmall : B < 3
  · rw [previousNonOneEnvelope, ite_eq_left hsmall]
    simpa only [(witnessMaxima_eq_zero_of_small hsmall).2, Nat.cast_zero] using (le_refl (0 : ℝ))
  · let L := Real.log B
    let C := min (preciseSavingEnvelope B) (neOneScaleBound B)
    have hC : (QNeOne B : ℝ) ≤ C :=
      le_min ((Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_preciseSaving B hGRH))
        (QNeOne_le_principal_scale B hGRH)
    have h0 : (QNeOne B : ℝ) ≤ (if B < 10 then 5 else L ^ 2) := by
      split_ifs with h
      · exact previous_nonOne_small h
      · exact QNeOne_le_log_sq_of_grh hGRH (Nat.le_of_not_lt h)
    have h1 : (QNeOne B : ℝ) ≤ (if 2984 ≤ B then (L - 1 / 1000) ^ 2 else C) := by
      split_ifs with h
      · exact QNeOne_le_retained_reciprocal_shift_of_ge_2984 h hGRH
      · exact hC
    have h2 : (QNeOne B : ℝ) ≤ (if 3295 ≤ B then (L - 1 / 10) ^ 2 else C) := by
      split_ifs with h
      · exact QNeOne_le_deci_shift_of_ge_3295 h hGRH
      · exact hC
    have h3 : (QNeOne B : ℝ) ≤ (if (25 / 2 : ℝ) ≤ L then (L - 1 / 2) ^ 2 else C) := by
      split_ifs with h
      · exact QNeOne_le_half_shift h hGRH
      · exact hC
    have h4 : (QNeOne B : ℝ) ≤ (if (16 : ℝ) ≤ L then (L - Real.log L + 3) ^ 2 else C) := by
      split_ifs with h
      · exact QNeOne_le_log_shift h hGRH
      · exact hC
    have h5 : (QNeOne B : ℝ) ≤ (if (96 : ℝ) ≤ L then (L - Real.log L + 11 / 4) ^ 2 else C) := by
      split_ifs with h
      · exact
          QNeOne_cast_le_elevenFourths_log_shift_from_96
            (previous_positive_of_log ((by norm_num only : (0 : ℝ) < 96).trans_le h)) hGRH h
      · exact hC
    have h6 : (QNeOne B : ℝ) ≤ (if (50 : ℝ) ≤ L then (L - 2 * Real.log L + 37 / 5) ^ 2 else C) := by
      split_ifs with h
      · exact QNeOne_le_shiftedDoubleLog_from_fifty h hGRH
      · exact hC
    have h7 : (QNeOne B : ℝ) ≤ (if (500 : ℝ) ≤ L then eulerPrefixTwoPoleNeOneRadius L else C) := by
      split_ifs with h
      · exact QNeOne_le_eulerPrefixTwoPole h hGRH
      · exact hC
    have h8 : (QNeOne B : ℝ) ≤ (if B < 1000000 then 47 else C) := by
      split_ifs with h
      · exact Nat.cast_le.mpr (QNeOne_le_fortySeven h)
      · exact hC
    have h9 :
      (QNeOne B : ℝ) ≤
        (if (3259 / 25 : ℝ) ≤ L ∧ L ≤ 16277 / 100 then
          (LLS.PaperStatements.oddMidscaleEndpointRadius L) ^ 2
        else C) := by
      split_ifs with h
      · exact QNeOne_le_oddMidscale hGRH h.1 h.2
      · exact hC
    rw [previousNonOneEnvelope, ite_eq_right hsmall]
    exact
      le_min h0
        (le_min h1
          (le_min h2
            (le_min h3
              (le_min h4 (le_min h5 (le_min h6 (le_min h7 (le_min h8 (le_min h9 (hC))))))))))

/-- Under GRH, the selected negative envelope bounds the actual cumulative maximum.
Intersect the complete preceding envelope with the proved Abel bound.
Role: the final negative Jacobi interface at every natural endpoint. -/
theorem QNegOne_le_fourPoleAbelEnvelope (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleAbelNegEnvelope B := by
  exact le_min (QNegOne_le_preciseSaving B hGRH) (QNegOne_le_fourPole_abel B hGRH)

/-- Under GRH, the selected non-one envelope bounds the actual cumulative maximum.
Intersect its full preceding model with the actual Abel estimate.
Role: the final non-one interface without weakening its dedicated candidates. -/
theorem QNeOne_le_fourPoleAbelEnvelope (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ fourPoleAbelNeEnvelope B := by
  exact le_min (QNeOne_le_previousNonOne B hGRH) (witnessMaxima_le_fourPole_abel B hGRH).2

/-- At every endpoint the selected negative envelope does not exceed its predecessor.
Project from the defining minimum. Role: unconditional full-domain non-worsening. -/
theorem fourPoleAbelNeg_le_previous (B : ℕ) :
    fourPoleAbelNegEnvelope B ≤ preciseSavingEnvelope B := by exact min_le_left _ _

/-- At every endpoint the selected non-one envelope does not exceed its predecessor.
Project from the defining minimum. Role: retain all old direct non-one candidates. -/
theorem fourPoleAbelNe_le_previous (B : ℕ) :
    fourPoleAbelNeEnvelope B ≤ previousNonOneEnvelope B := by exact min_le_left _ _

/-- From endpoint three the selected negative envelope absorbs exceptional stop 27.
Combine the preceding floor 31 with the Abel floor 27.
Role: transfer the final minimum to both negative Selfridge scans. -/
theorem fourPoleAbelNeg_ge_twenty_seven {B : ℕ} (hB : 3 ≤ B) :
    (27 : ℝ) ≤ fourPoleAbelNegEnvelope B := by
  exact
    le_min ((by norm_num only : (27 : ℝ) ≤ 31).trans (preciseEnvelope_ge_thirty_one hB))
      (fourPole_abel_ge_twenty_seven B)

/-- For nonnegative coefficient and lower entrance, increasing the entrance enlarges
the log-scale bound. Compare the maxima, their squares and the coefficient products.
Role: compare the new and preceding three-row candidates at all endpoints. -/
private theorem abel_scale_monotone {c E₁ E₂ : ℝ} (hc : 0 ≤ c) (hE : 0 ≤ E₁) (hE12 : E₁ ≤ E₂)
    (B : ℕ) : logScaleBound c E₁ B ≤ logScaleBound c E₂ B := by
  have hm := max_le_max hE12 (le_refl (Real.log B))
  have hz : 0 ≤ max E₁ (Real.log B) := hE.trans (le_max_left _ _)
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hz (hz.trans hm)).mpr hm) hc

/-- At every endpoint the new three-row Abel minimum improves the preceding rows.
Compare the equal coefficients and smaller certified entrances row by row.
Role: preserve the whole preceding fourth-pole candidate without asymptotic restrictions. -/
theorem fourPoleAbel_le_old_rows (B : ℕ) : fourPoleAbelBound B ≤ fourPoleReducedBound B := by
  have h0 :
    fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel777 B ≤
      fourPoleEntranceBound LLS.PaperStatements.fourPole777Entrance B := by
    change
      logScaleBound (777 / 1000) ((40000 : ℝ) ^ 2) B ≤
        logScaleBound (777 / 1000) ((1200000 : ℝ) ^ 2) B
    exact abel_scale_monotone (by norm_num only) (by norm_num only) (by norm_num only) B
  have h1 :
    fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel78 B ≤
      fourPoleEntranceBound LLS.PaperStatements.fourPole78Entrance B := by
    change logScaleBound (39 / 50) ((5000 : ℝ) ^ 2) B ≤ logScaleBound (39 / 50) ((120000 : ℝ) ^ 2) B
    exact abel_scale_monotone (by norm_num only) (by norm_num only) (by norm_num only) B
  have h2 :
    fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel79 B ≤
      fourPoleEntranceBound LLS.PaperStatements.fourPole79Entrance B := by
    change
      logScaleBound (79 / 100) ((2000 : ℝ) ^ 2) B ≤ logScaleBound (79 / 100) ((30000 : ℝ) ^ 2) B
    exact abel_scale_monotone (by norm_num only) (by norm_num only) (by norm_num only) B
  exact min_le_min h0 (min_le_min h1 h2)

/-- A log-scale candidate with coefficient at least four fifths covers four fifths
of the endpoint log squared. Square the maximum comparison.
Role: common candidate floors in the strict winning interval. -/
private theorem abel_window_scale_floor {c E : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (B : ℕ) :
    (4 / 5 : ℝ) * Real.log B ^ 2 ≤ logScaleBound c E B := by
  have hL := Real.log_natCast_nonneg B
  have hm := le_max_right E (Real.log B)
  have hs := (sq_le_sq₀ hL (hL.trans hm)).mpr hm
  exact
    (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 4 / 5)).trans
      (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

/-- Each preceding row exceeds four fifths of log squared when the log is at most
ten million. Its certified entrance is at least one hundred million.
Compare squared scales and the original coefficient floor; retain all old rows. -/
private theorem abel_window_old_row_floor (f : LLS.PaperStatements.FourPoleEntry) {B : ℕ}
    (hU : Real.log B ≤ 10000000) : (4 / 5 : ℝ) * Real.log B ^ 2 ≤ fourPoleEntranceBound f B := by
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg B) (by norm_num only : (0 : ℝ) ≤ 10000000)).mpr hU
  have hm : (100000000 : ℝ) ≤ max (f.rootEntrance ^ 2) (Real.log B) :=
    (LLS.PaperStatements.fourPole_data_scale_lower f).trans (le_max_left _ _)
  have hsq :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 100000000)
          ((by norm_num only : (0 : ℝ) ≤ 100000000).trans hm)).mpr
      hm
  have hlarge :=
    mul_le_mul_of_nonneg_right f.coefficient_lower
      (sq_nonneg (max (f.rootEntrance ^ 2) (Real.log B)))
  change (4 / 5 : ℝ) * Real.log B ^ 2 ≤ f.coefficient * max (f.rootEntrance ^ 2) (Real.log B) ^ 2
  nlinarith only [hs, hsq, hlarge]

/-- A logarithm at least four million forces the endpoint above one million.
Use log x at most x minus one. Role: discharge finite-cap guards in the winning window. -/
private theorem abel_window_large_endpoint {B : ℕ} (hL : 4000000 ≤ Real.log B) : 1000000 ≤ B := by
  have hp := previous_positive_of_log ((by norm_num only : (0 : ℝ) < 4000000).trans_le hL)
  have hl := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hp : (0 : ℝ) < B)
  exact Nat.cast_le.mp (by linarith only [hL, hl] : (1000000 : ℝ) ≤ B)

/-- In the winning window the refined elementary radius covers log squared.
Expand log(4B); both logarithmic corrections are nonnegative.
Role: retain the elementary candidate in the complete negative baseline. -/
private theorem abel_window_elementary_floor {B : ℕ} (hL : 4000000 ≤ Real.log B) :
    Real.log B ^ 2 ≤ refinedElementaryRadius B := by
  have hp := previous_positive_of_log ((by norm_num only : (0 : ℝ) < 4000000).trans_le hL)
  have he := Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hp).ne'
  have h4 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 4)
  have hh : (1 : ℝ) ≤ Real.log (4 * (B : ℝ)) := by
    rw [he]
    linarith only [h4, hL]
  have hl := Real.log_nonneg hh
  rw [he] at hl
  change
    Real.log B ^ 2 ≤
      (Real.log (4 * (B : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (B : ℝ))) + 2) ^ 2
  apply (sq_le_sq₀ (Real.log_natCast_nonneg B) _).mpr
  · rw [he]
    linarith only [h4, hl]
  · rw [he]
    linarith only [h4, hl, hL]

/-- On scales at least ten thousand, the logarithm uses at most one percent of the scale.
Input: the lower scale bound. Claim: a uniform logarithmic cap.
Proof: use the existing square-root bound and square the linear comparison.
Role: all shifted and logarithmic direct-candidate lower bounds in these windows. -/
private theorem abel_old_log_cap {L : ℝ} (hL : 10000 ≤ L) : Real.log L ≤ L / 100 := by
  have h0 := (by norm_num only : (0 : ℝ) ≤ 10000).trans hL
  have hm := mul_le_mul_of_nonneg_right hL h0
  have hs : Real.sqrt L ≤ L / 100 :=
    Real.sqrt_le_iff.mpr ⟨div_nonneg h0 (by norm_num only : (0 : ℝ) ≤ 100), by nlinarith only [hm]⟩
  exact (Analysis.log_le_sqrt_of_pos ((by norm_num only : (0 : ℝ) < 10000).trans_le hL)).trans hs

/-- A root above 98 percent of a nonnegative scale has square above nine tenths.
Input: a scale and a lower root comparison. Claim: the squared floor.
Proof: square and compare rational coefficients. Role: earlier direct non-one candidates. -/
private theorem abel_old_square_floor {L r : ℝ} (hL : 0 ≤ L) (hr : (49 / 50 : ℝ) * L ≤ r) :
    (9 / 10 : ℝ) * L ^ 2 ≤ r ^ 2 := by
  have h0 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 49 / 50) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- Either two-pole leading term has coefficient above nine tenths after squaring.
Input: a nonnegative scale and root covering its linear term. Claim: the radius floor.
Proof: exact rational squared comparison. Role: both former two-pole branches. -/
private theorem abel_old_twoPole_floor {L r : ℝ} (hL : 0 ≤ L) (hr : (500 / 821 : ℝ) * L ≤ r) :
    (9 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * r ^ 2 := by
  have h0 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 500 / 821) hL
  have hs := (sq_le_sq₀ h0 (h0.trans hr)).mpr hr
  nlinarith only [hs, sq_nonneg L]

/-- Every active direct non-one branch exceeds nine tenths after logarithmic scale 21000.
Input: that lower endpoint. Claim: the complete earlier tail has the stated floor.
Proof: bound logarithmic corrections and check the two-pole leading coefficient.
Role: a whole-minimum lower certificate for the dedicated non-one Gamma candidate. -/
private theorem abel_old_neOne_floor {B : ℕ} (hL : 21000 ≤ Real.log B) :
    (9 / 10 : ℝ) * Real.log B ^ 2 ≤ legacyNeOneTail B := by
  have h0 := Real.log_natCast_nonneg B
  have hl := abel_old_log_cap ((by norm_num only : (10000 : ℝ) ≤ 21000).trans hL)
  have h1 :=
    abel_old_square_floor h0 (by linarith only [h0] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B)
  have h2 :=
    abel_old_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 1000)
  have h3 :=
    abel_old_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 10)
  have h4 :=
    abel_old_square_floor h0
      (by linarith only [hL] : (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 1 / 2)
  have h5 :=
    abel_old_square_floor h0
      (by linarith only [hl, h0] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - Real.log (Real.log B) + 3)
  have h6 :=
    abel_old_square_floor h0
      (by linarith only [hl, h0] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - Real.log (Real.log B) + 11 / 4)
  have h7 :=
    abel_old_square_floor h0
      (by linarith only [hl] :
        (49 / 50 : ℝ) * Real.log B ≤ Real.log B - 2 * Real.log (Real.log B) + 37 / 5)
  have hp : (9 / 10 : ℝ) * Real.log B ^ 2 ≤ eulerPrefixTwoPoleNeOneRadius (Real.log B) :=
    abel_old_twoPole_floor h0 (by linarith only)
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

/-- For endpoint logarithms from four million through ten million, the complete
preceding negative minimum, including both Q5 radii, equals four fifths log squared.
Prove every guarded branch has that floor and select the existing Gamma candidate.
Role: a whole-minimum certificate rather than a comparison with selected old branches. -/
theorem abel_previous_negative_window {B : ℕ} (hL : 4000000 ≤ Real.log B)
    (hU : Real.log B ≤ 10000000) : preciseSavingEnvelope B = (4 / 5 : ℝ) * Real.log B ^ 2 := by
  let L := Real.log B
  let T := (4 / 5 : ℝ) * L ^ 2
  have h0 := Real.log_natCast_nonneg B
  have hB := abel_window_large_endpoint hL
  have h750 : ¬B < 750 := Nat.not_lt.mpr ((by norm_num only : (750 : ℕ) ≤ 1000000).trans hB)
  have h500 : (500 : ℝ) ≤ L := (by norm_num only : (500 : ℝ) ≤ 4000000).trans hL
  have h64 : ¬Real.log B ≤ 1609 / 25 := by linarith only [hL]
  have hsmall : T ≤ L ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) (by norm_num only : (4 / 5 : ℝ) ≤ 1)
  have hj : T ≤ jointEndpointBound B :=
    abel_window_scale_floor (by norm_num only : (4 / 5 : ℝ) ≤ 9999 / 10000) B
  have hc : T ≤ commonEndpointEnvelope B := by
    change
      T ≤
        min (refinedElementaryRadius B)
          (min (jointEndpointBound B)
            (if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B))
    rw [ite_eq_right h64]
    exact le_min (hsmall.trans (abel_window_elementary_floor hL)) (le_min hj hj)
  have hf : T ≤ negOneEndpointEnvelope B := by
    change T ≤ min (commonEndpointEnvelope B) (if B < 750 then 31 else commonEndpointEnvelope B)
    rw [ite_eq_right h750]
    exact le_min hc hc
  have hk : T ≤ fourPoleReducedBound B :=
    le_min (abel_window_old_row_floor _ hU)
      (le_min (abel_window_old_row_floor _ hU) (abel_window_old_row_floor _ hU))
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ L + 7 / 5 by linarith only [hL])
  have hq : T ≤ quarterClippedTwoPoleNegOneRadius L := by
    have hp :=
      abel_old_twoPole_floor h0
        (show (500 / 821 : ℝ) * L ≤ LLS.quarterClippedNegativeRoot (L + 7 / 5)
          by
          dsimp only [LLS.quarterClippedNegativeRoot]
          linarith only [hl])
    exact
      (show T ≤ (9 / 10 : ℝ) * L ^ 2 by
            dsimp only [T]
            nlinarith only [sq_nonneg L]).trans
        hp
  have hn : T ≤ previousNegativeEnvelope B := by
    change
      T ≤
        min (negOneEndpointEnvelope B)
          (min (mixedScaleBound B)
            (min (negativeScaleBound B)
              (min (fourPoleReducedBound B)
                (if 500 ≤ Real.log B then quarterClippedTwoPoleNegOneRadius (Real.log B)
                else negOneEndpointEnvelope B))))
    rw [ite_eq_left h500]
    exact
      le_min hf
        (le_min (abel_window_scale_floor (by norm_num only) B)
          (le_min (abel_window_scale_floor (by norm_num only) B) (le_min hk hq)))
  apply le_antisymm
  · have hp : preciseSavingEnvelope B ≤ negativeScaleBound B :=
      (min_le_left _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have he : negativeScaleBound B = T := by
      change (4 / 5 : ℝ) * max 46000 L ^ 2 = T
      rw [max_eq_right ((by norm_num only : (46000 : ℝ) ≤ 4000000).trans hL)]
    exact hp.trans_eq he
  · exact
      le_min hn
        (le_min (hsmall.trans (log_sq_le_preciseRadii B).1)
          (hsmall.trans (log_sq_le_preciseRadii B).2))

/-- On the same continuous window the full preceding non-one minimum equals four
fifths log squared. Keep every direct candidate and discharge finite/bounded guards;
the direct tail is above nine tenths and the shared Gamma branch attains the floor.
Role: a complete non-one baseline certificate for the new Abel entrance. -/
theorem abel_previous_nonOne_window {B : ℕ} (hL : 4000000 ≤ Real.log B)
    (hU : Real.log B ≤ 10000000) : previousNonOneEnvelope B = (4 / 5 : ℝ) * Real.log B ^ 2 := by
  let L := Real.log B
  let T := (4 / 5 : ℝ) * L ^ 2
  let C := min (preciseSavingEnvelope B) (neOneScaleBound B)
  have hB := abel_window_large_endpoint hL
  have h3 : ¬B < 3 := Nat.not_lt.mpr ((by norm_num only : (3 : ℕ) ≤ 1000000).trans hB)
  have h10 : ¬B < 10 := Nat.not_lt.mpr ((by norm_num only : (10 : ℕ) ≤ 1000000).trans hB)
  have h2984 := (by norm_num only : (2984 : ℕ) ≤ 1000000).trans hB
  have h3295 := (by norm_num only : (3295 : ℕ) ≤ 1000000).trans hB
  have hmid : ¬((3259 / 25 : ℝ) ≤ L ∧ L ≤ 16277 / 100) := by
    intro h
    linarith only [hL, h.2]
  have hn : neOneScaleBound B = T := by
    change (4 / 5 : ℝ) * max 22221 L ^ 2 = T
    rw [max_eq_right ((by norm_num only : (22221 : ℝ) ≤ 4000000).trans hL)]
  have hC : C = T := by
    change min (preciseSavingEnvelope B) (neOneScaleBound B) = T
    rw [abel_previous_negative_window hL hU, hn, min_self]
  have ht := abel_old_neOne_floor ((by norm_num only : (21000 : ℝ) ≤ 4000000).trans hL)
  have hf : T ≤ legacyNeOneTail B := by
    exact
      (show T ≤ (9 / 10 : ℝ) * Real.log B ^ 2 by
            dsimp only [T, L]
            nlinarith only [sq_nonneg (Real.log B)]).trans
        ht
  have h50 : (50 : ℝ) ≤ L := (by norm_num only : (50 : ℝ) ≤ 4000000).trans hL
  have h16 : (16 : ℝ) ≤ L := (by norm_num only : (16 : ℝ) ≤ 4000000).trans hL
  have h96 : (96 : ℝ) ≤ L := (by norm_num only : (96 : ℝ) ≤ 4000000).trans hL
  have hhalf : (25 / 2 : ℝ) ≤ L := (by norm_num only : (25 / 2 : ℝ) ≤ 4000000).trans hL
  have h500 : (500 : ℝ) ≤ L := (by norm_num only : (500 : ℝ) ≤ 4000000).trans hL
  rw [previousNonOneEnvelope, ite_eq_right h3]
  dsimp only
  rw [ite_eq_right h10, ite_eq_left h2984, ite_eq_left h3295, ite_eq_left hhalf, ite_eq_left h16,
    ite_eq_left h96, ite_eq_left h50, ite_eq_left h500, ite_eq_right (Nat.not_lt.mpr hB),
    ite_eq_right hmid]
  change
    min (L ^ 2)
        (min ((L - 1 / 1000) ^ 2)
          (min ((L - 1 / 10) ^ 2)
            (min ((L - 1 / 2) ^ 2)
              (min ((L - Real.log L + 3) ^ 2)
                (min ((L - Real.log L + 11 / 4) ^ 2)
                  (min ((L - 2 * Real.log L + 37 / 5) ^ 2)
                    (min (eulerPrefixTwoPoleNeOneRadius L) (min C (min C C))))))))) =
      T
  rw [hC]
  apply le_antisymm
  · exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
  · exact
      (le_min (hf.trans (min_le_left _ _))
        (le_min (hf.trans ((min_le_right _ _).trans (min_le_left _ _)))
          (le_min (hf.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
            (le_min
              (hf.trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
              (le_min
                (hf.trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans
                      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
                (le_min
                  (hf.trans
                    ((min_le_right _ _).trans
                      ((min_le_right _ _).trans
                        ((min_le_right _ _).trans
                          ((min_le_right _ _).trans
                            ((min_le_right _ _).trans (min_le_left _ _)))))))
                  (le_min
                    (hf.trans
                      ((min_le_right _ _).trans
                        ((min_le_right _ _).trans
                          ((min_le_right _ _).trans
                            ((min_le_right _ _).trans
                              ((min_le_right _ _).trans
                                ((min_le_right _ _).trans (min_le_left _ _))))))))
                    (le_min
                      (hf.trans
                        ((min_le_right _ _).trans
                          ((min_le_right _ _).trans
                            ((min_le_right _ _).trans
                              ((min_le_right _ _).trans
                                ((min_le_right _ _).trans
                                  ((min_le_right _ _).trans
                                    ((min_le_right _ _).trans (min_le_left _ _)))))))))
                      (le_min (le_refl T) (le_min (le_refl T) (le_refl T)))))))))))

/-- Throughout the continuous logarithmic window [four million, ten million], both
new public envelopes strictly improve their complete preceding minima.
The new 79/100 row is active and strictly below the preceding four-fifths value.
Role: certify strict improvement of both semantics under the full candidate model. -/
theorem fourPoleAbel_strict_window {B : ℕ} (hL : 4000000 ≤ Real.log B)
    (hU : Real.log B ≤ 10000000) :
    fourPoleAbelNegEnvelope B < preciseSavingEnvelope B ∧
      fourPoleAbelNeEnvelope B < previousNonOneEnvelope B := by
  have hrow : fourPoleAbelBound B ≤ (79 / 100 : ℝ) * Real.log B ^ 2 := by
    have hm : fourPoleAbelBound B ≤ fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel79 B :=
      (min_le_right _ _).trans (min_le_right _ _)
    have he :
      fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel79 B =
        (79 / 100 : ℝ) * Real.log B ^ 2 := by
      change (79 / 100 : ℝ) * max ((2000 : ℝ) ^ 2) (Real.log B) ^ 2 = _
      rw [max_eq_right
          (by
            norm_num only [Nat.cast_ofNat] at hL ⊢; exact hL)]
    exact hm.trans_eq he
  have hs : (79 / 100 : ℝ) * Real.log B ^ 2 < (4 / 5 : ℝ) * Real.log B ^ 2 := by
    have hp : 0 < Real.log B := (by norm_num only : (0 : ℝ) < 4000000).trans_le hL
    nlinarith only [sq_pos_of_pos hp]
  rw [abel_previous_negative_window hL hU, abel_previous_nonOne_window hL hU]
  exact ⟨((min_le_right _ _).trans hrow).trans_lt hs, ((min_le_right _ _).trans hrow).trans_lt hs⟩

/-- For an odd nonsquare under GRH, both actual least Jacobi primes satisfy their
respective selected envelopes. Embed the input in each cumulative maximum.
Role: retain the same-modulus least-prime interpretation of the final minima. -/
theorem leastWitnesses_le_abelEnvelope {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fourPoleAbelNegEnvelope n ∧
      (NumberTheory.primeNeOneWitness n (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw) :
          ℝ) ≤
        fourPoleAbelNeEnvelope n := by
  have hm := NumberTheory.mem_admissibleFinset_iff.mpr ⟨hn.pos, le_rfl, hn, hns⟩
  exact
    ⟨(Nat.cast_le.mpr (primeNegOneWitness_le_QNegOne hm)).trans
        (QNegOne_le_fourPoleAbelEnvelope n hGRH),
      (Nat.cast_le.mpr (primeNeOneWitness_le_QNeOne hm)).trans
        (QNeOne_le_fourPoleAbelEnvelope n hGRH)⟩

/-- Under GRH, an odd nonsquare has actual negative and non-one Jacobi primes
below their respective final minima. Choose the canonical bounded least witnesses.
Role: a closed actual-prime interface with no scalar certificate left as an input. -/
theorem existsWitnesses_le_abelEnvelope {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ fourPoleAbelNegEnvelope n) ∧
      (∃ p : ℕ, p ∈ NumberTheory.primeNeOneWitnessSet n ∧ (p : ℝ) ≤ fourPoleAbelNeEnvelope n) := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  let hv := NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw
  have h := leastWitnesses_le_abelEnvelope hn hns hGRH hw
  exact
    ⟨⟨NumberTheory.primeNegOneWitness n hw, NumberTheory.primeNegOneWitness_mem n hw, h.1⟩,
      ⟨NumberTheory.primeNeOneWitness n hv, NumberTheory.primeNeOneWitness_mem n hv, h.2⟩⟩

end PseudoPrime.PseudoSquare
