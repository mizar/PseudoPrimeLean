/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicShiftBounds

/-! # Logarithmic profiles which stay below the logarithmic square -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: positive endpoints with L0 at most L.
Claim: log increments lie below their chord bound.
Proof: apply log(t) at most t minus one and clear the positive denominator.
This supports endpoint certificates for all later logarithmic inputs. -/
theorem log_increment_mul_lower_le {L0 L : ℝ} (h0 : 0 < L0) (hL : L0 ≤ L) :
    (Real.log L - Real.log L0) * L0 ≤ L - L0 := by
  have h := Real.log_le_sub_one_of_pos (div_pos (h0.trans_le hL) h0)
  rw [Real.log_div (h0.trans_le hL).ne' h0.ne'] at h
  have hm := mul_le_mul_of_nonneg_right h h0.le
  have he : (L / L0 - 1) * L0 = L - L0 := by rw [sub_mul, div_mul_cancel₀ _ h0.ne', one_mul]
  rw [he] at hm
  exact hm

/-- Input: a positive starting input, a nonnegative ray slope, and correction
b log L0 plus c below that ray, with b at most d times L0.
Claim: the correction stays below the ray at every later input.
Proof: split on the sign of b and use the logarithmic chord bound.
This excludes a later crossing above the logarithmic square. -/
theorem logarithmic_correction_le_ray {L0 L b c d : ℝ} (h0 : 0 < L0) (hL : L0 ≤ L) (hd : 0 ≤ d)
    (hb : b ≤ d * L0) (hc : b * Real.log L0 + c ≤ d * L0) : b * Real.log L + c ≤ d * L := by
  by_cases hb0 : b ≤ 0
  · have hm := mul_le_mul_of_nonpos_left (Real.log_le_log h0 hL) hb0
    have hdL := mul_le_mul_of_nonneg_left hL hd
    linarith only [hm, hdL, hc]
  · have hinc := mul_le_mul_of_nonneg_left (log_increment_mul_lower_le h0 hL) (le_of_not_ge hb0)
    have hratio := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hL)
    have hscaled : L0 * (b * (Real.log L - Real.log L0)) ≤ L0 * (d * (L - L0)) := by
      nlinarith only [hinc, hratio]
    have hdiff := le_of_mul_le_mul_left hscaled h0
    linarith only [hdiff, hc]

/-- Input: positive rational a, nonnegative d with a times (1+d) squared below one,
a positive start, an increasing nonnegative root, and an endpoint ray certificate.
Claim: the profile is strictly below L squared at every later input.
Proof: propagate the ray certificate and compare nonnegative squares.
This certifies the whole tail without sampling crossings. -/
theorem logarithmicShiftCutoff_lt_sq_of_ray {L0 L : ℝ} {a b c d : ℚ} (ha : 0 < a) (hd : 0 ≤ d)
    (hf : (a : ℝ) * (1 + (d : ℝ)) ^ 2 < 1) (h0 : 0 < L0) (hL : L0 ≤ L) (hblo : -L0 ≤ (b : ℝ))
    (hbhi : (b : ℝ) ≤ (d : ℝ) * L0) (hr : 0 ≤ logarithmicShiftRoot L0 b c)
    (hc : (b : ℝ) * Real.log L0 + (c : ℝ) ≤ (d : ℝ) * L0) :
    logarithmicShiftCutoff L a b c < L ^ 2 := by
  have hroot := logarithmicShiftRoot_le_of_le (c := c) h0 hL hblo
  have hcorr := logarithmic_correction_le_ray h0 hL (Rat.cast_nonneg.mpr hd) hbhi hc
  have hupper : logarithmicShiftRoot L b c ≤ (1 + (d : ℝ)) * L := by
    dsimp only [logarithmicShiftRoot]
    linarith only [hcorr]
  have hsq := (sq_le_sq₀ (hr.trans hroot) ((hr.trans hroot).trans hupper)).mpr hupper
  calc
    logarithmicShiftCutoff L a b c ≤ (a : ℝ) * ((1 + (d : ℝ)) * L) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (Rat.cast_nonneg.mpr ha.le)
    _ = ((a : ℝ) * (1 + (d : ℝ)) ^ 2) * L ^ 2 := by ring
    _ < 1 * L ^ 2 := mul_lt_mul_of_pos_right hf (sq_pos_of_pos (h0.trans_le hL))
    _ = L ^ 2 := one_mul _

/-- A constant-shift candidate for a scale threshold of twenty thousand.
The coefficient is four fifths and the shift is 105/4. This is a numerical
profile, not an assertion that any witness is bounded by it. -/
noncomputable def gammaSubsquareCandidate (L : ℝ) : ℝ :=
  logarithmicShiftCutoff L (4 / 5) 0 (105 / 4)

/-- Input: L at least 445/2.
Claim: the candidate stays strictly below L squared on the whole tail.
Proof: use a rational ray slope of 59/500 in the generic theorem.
This certifies comparison of formulas independently of witness existence. -/
theorem gamma_subsquare_candidate_lt {L : ℝ} (hL : (445 / 2 : ℝ) ≤ L) :
    gammaSubsquareCandidate L < L ^ 2 := by
  apply
    logarithmicShiftCutoff_lt_sq_of_ray (d := 59 / 500) (L0 := 445 / 2) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) hL
  · norm_num only
  · norm_num only
  · norm_num only [logarithmicShiftRoot, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat, zero_mul,
      add_zero]
  · norm_num only [zero_mul, zero_add]

/-- Input: L at least 445/2.
Claim: the candidate cutoff is at least 198005/4.
Proof: use monotonicity of the nonnegative shifted square.
This provides finite-prefix and scale eligibility at every later input. -/
theorem gamma_subsquare_candidate_lower {L : ℝ} (hL : (445 / 2 : ℝ) ≤ L) :
    (198005 / 4 : ℝ) ≤ gammaSubsquareCandidate L := by
  have h :=
    logarithmicShiftCutoff_le_of_le (a := 4 / 5) (b := 0) (c := 105 / 4) (by norm_num only)
      (by norm_num only : (0 : ℝ) < 445 / 2) hL (by norm_num only)
      (by
        norm_num only [logarithmicShiftRoot, Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat, zero_mul,
          add_zero])
  norm_num only [logarithmicShiftCutoff, logarithmicShiftRoot, Rat.cast_zero, Rat.cast_div,
    Rat.cast_ofNat, zero_mul, add_zero] at h
  norm_num only [gammaSubsquareCandidate, logarithmicShiftCutoff, logarithmicShiftRoot,
    Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat, zero_mul, add_zero]
  exact h

/-- Input: L at least 445/2.
Claim: prefix 45000 and scale 20000 are compatible with the candidate cutoff.
Proof: use its exact rational lower endpoint.
These are eligibility conditions, not the missing analytic witness gap. -/
theorem gamma_subsquare_candidate_eligible {L : ℝ} (hL : (445 / 2 : ℝ) ≤ L) :
    45000 ≤ gammaSubsquareCandidate L ∧ 20000 ≤ (40 / 99 : ℝ) * gammaSubsquareCandidate L := by
  have h := gamma_subsquare_candidate_lower hL
  constructor
  · linarith only [h]
  · linarith only [h]

/-- Input: a quadratic with leading coefficient below one, a strict endpoint
comparison and a nonnegative derivative of the difference at that endpoint.
Claim: the quadratic stays below L squared for every later input.
Proof: expand the difference using L minus its lower endpoint.
This supports independent coefficients instead of a squared shifted root. -/
theorem quadratic_profile_lt_sq_on_tail {a u v L0 L : ℝ} (ha : a < 1) (hL : L0 ≤ L)
    (hu : u ≤ 2 * (1 - a) * L0) (hstart : a * L0 ^ 2 + u * L0 + v < L0 ^ 2) :
    a * L ^ 2 + u * L + v < L ^ 2 := by
  have hd := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hL)
  have hs := mul_nonneg (sub_pos.mpr ha).le (sq_nonneg (L - L0))
  nlinarith only [hstart, hd, hs]

end PseudoPrime.Analysis
