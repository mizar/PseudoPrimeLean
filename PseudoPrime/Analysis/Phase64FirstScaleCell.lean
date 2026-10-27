/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalLogScaleIntervals
public import PseudoPrime.Analysis.ScaledGammaPhaseNodes

/-! # A continuous Gamma phase rectangle in the first level cell -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real scale between the exact images of levels 64 and 64.001.
Claim: log(256*x) lies in the displayed rational interval throughout the cell.
Proof: certify both rational endpoints and use the general logarithm enclosure theorem.
Role: supply the transcendental premise for the first actual level cell. -/
theorem log_phase_scale64_small_cell {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) :
    (1295670321 / 100000000 : ℝ) ≤ Real.log (256 * x) ∧
      Real.log (256 * x) ≤ (1295673447 / 100000000 : ℝ) := by
  have hA :
    rationalLogIntervalCheck (41943040 / 99) 18 48 (1295670321 / 100000000)
        (1295670322 / 100000000) =
      true := by
    decide +kernel
  have hB :
    rationalLogIntervalCheck (131076096032 / 309375) 18 48 (1295673446 / 100000000)
        (1295673447 / 100000000) =
      true := by
    decide +kernel
  have ha : ((41943040 / 99 : ℚ) : ℝ) ≤ 256 * x := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hlo]
  have hb : 256 * x ≤ ((131076096032 / 309375 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hhi]
  have h := log_enclosure_on_rational_interval hA hB ha hb
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Input: a rational ordinate. Output: its product with the logarithmic cell midpoint.
Role: compute phase centers uniformly for every scale in the cell. -/
def phaseCell64Center (t : ℚ) : ℚ :=
  t * ((1295670321 / 100000000 + 1295673447 / 100000000) / 2)

/-- Input: a rational ordinate. Output: its magnitude times half the logarithmic cell width.
Role: include continuous scale uncertainty in each rational endpoint check. -/
def phaseCell64Uncertainty (t : ℚ) : ℚ :=
  |t| * ((1295673447 / 100000000 - 1295670321 / 100000000) / 2)

/-- Input: an integer grid index k. Output: whether the center is valid and the rational gap
is at least 141/10^6 at k/2000. Role: certify endpoints without storing expanded arithmetic. -/
def phaseCell64NodeCheck (k : ℕ) : Bool :=
  let t : ℚ := k / 2000
  decide
    (|phaseCell64Center t| ≤ 64 ∧
      (141 / 1000000 : ℚ) ≤
        rationalScaledPhase64Lower (10 ^ 12) t (phaseCell64Center t) (phaseCell64Uncertainty t))

/-- Claim: all nine endpoint checks with indices 4356 through 4364 succeed.
Proof: compute the fixed evaluator in the kernel without resource overrides.
Role: supply eight adjacent continuous ordinate intervals. -/
theorem phaseCell64_checked_nodes : (List.range' 4356 9).all phaseCell64NodeCheck = true := by
  decide +kernel

/-- Input: a scale in the cell and one of the nine certified indices.
Claim: the actual Gamma-resolvent gap at that node is at least 1/10000.
Proof: combine the uniform logarithm interval, rational checks and Gamma approximation error.
Role: discharge both endpoints of the continuous moment interpolation. -/
theorem phaseCell64_node_gap {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) (k : ℕ) (hk : k ∈ List.range' 4356 9) :
    (1 / 10000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients ((k / 2000 : ℚ) : ℝ) +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ((k / 2000 : ℚ) : ℂ)) *
            (x : ℂ) ^ (Complex.I * ((k / 2000 : ℚ) : ℂ))).re := by
  have hcheck := List.all_eq_true.mp phaseCell64_checked_nodes k hk
  have hc :
    |phaseCell64Center (k / 2000)| ≤ 64 ∧
      (141 / 1000000 : ℚ) ≤
        rationalScaledPhase64Lower (10 ^ 12) (k / 2000) (phaseCell64Center (k / 2000))
          (phaseCell64Uncertainty (k / 2000)) :=
    of_decide_eq_true hcheck
  obtain ⟨hl, hu⟩ := log_phase_scale64_small_cell hlo hhi
  have hlQ : ((1295670321 / 100000000 : ℚ) : ℝ) ≤ Real.log (256 * x) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact hl
  have huQ : Real.log (256 * x) ≤ ((1295673447 / 100000000 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact hu
  have he := phase_enclosure_of_rational_log_interval hlQ huQ (k / 2000)
  change
    |((k / 2000 : ℚ) : ℝ) * Real.log (256 * x) - (phaseCell64Center (k / 2000) : ℝ)| ≤
      (phaseCell64Uncertainty (k / 2000) : ℝ) at he
  have hvR := (Rat.cast_le (K := ℝ)).mpr hc.1
  norm_num only [Rat.cast_abs, Rat.cast_ofNat] at hvR
  have hlow :=
    rationalScaledPhase64Lower_le (10 ^ 12) (k / 2000) (phaseCell64Center (k / 2000))
      (phaseCell64Uncertainty (k / 2000)) (hvR.trans (by norm_num only : (64 : ℝ) ≤ 128)) he
  have hr := (Rat.cast_le (K := ℝ)).mpr hc.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hk
  have hik : k < 4365 := by
    rw [heq]
    simp only [one_mul]
    exact Nat.add_lt_add_left hi 4356
  have hkR : (k : ℝ) < 4365 := Nat.cast_lt.mpr hik
  apply
    phase64_actual_gap_ge_of_rounded_node
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 163840 / 99) hlo)
      (by norm_num only : 0 < 10 ^ 12) (k / 2000)
      (by
        norm_num only [Rat.cast_div, Rat.cast_natCast, abs_div,
          abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k), abs_of_pos]
        linarith only [hkR])
  have hb :
    (1 / 10000 : ℝ) + (1 / 25000 + 32768 / ((10 ^ 12 : ℕ) : ℝ)) ≤
      (rationalScaledPhase64Lower (10 ^ 12) (k / 2000) (phaseCell64Center (k / 2000))
          (phaseCell64Uncertainty (k / 2000)) :
        ℝ) := by
    norm_num only
    linarith only [hr]
  exact hb.trans hlow

/-- Input: a scale in the cell. Claim: its absolute logarithm is at most eight.
Proof: use the certified phase logarithm and a lower bound for log(256).
Role: discharge the Gamma logarithmic moment hypothesis. -/
theorem log_scale64_small_cell_abs_le_eight {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) : |Real.log x| ≤ 8 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num only) hlo
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hlo])
  have hu := (log_phase_scale64_small_cell hlo hhi).2
  rw [Real.log_mul (by norm_num only : (256 : ℝ) ≠ 0) hx.ne'] at hu
  have h256 : (5 : ℝ) ≤ Real.log 256 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  rw [abs_of_nonneg hl]
  linarith only [hu, h256]

/-- Input: a scale in the cell and one of the eight adjacent ordinate intervals.
Claim: the actual Gamma-resolvent gap is at least 533/8000000 throughout that interval.
Proof: interpolate the certified endpoints using the moment and curvature bounds.
Role: remove the ordinate sampling premise from this part of the spectral region. -/
theorem phaseCell64_gap_on_checked_interval {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) (i : ℕ) (hi : i < 8) {t : ℝ}
    (ht : t ∈ Set.Icc (((4356 + i : ℕ) : ℝ) / 2000) (((4357 + i : ℕ) : ℝ) / 2000)) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have hA :=
    phaseCell64_node_gap hlo hhi (4356 + i)
      (List.mem_range'.mpr ⟨i, Nat.lt_trans hi (by norm_num only : 8 < 9), by ring⟩)
  have hB :=
    phaseCell64_node_gap hlo hhi (4357 + i)
      (List.mem_range'.mpr ⟨i + 1, Nat.succ_lt_succ hi, by ring⟩)
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hA hB
  have hab : (((4356 + i : ℕ) : ℝ) / 2000) < (((4357 + i : ℕ) : ℝ) / 2000) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith only
  have hw : (((4357 + i : ℕ) : ℝ) / 2000) - (((4356 + i : ℕ) : ℝ) / 2000) ≤ 1 / 2000 := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith only
  have h :=
    phase64_gap_lower_on_small_interval (t := t)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 163840 / 99) hlo)
      (log_scale64_small_cell_abs_le_eight hlo hhi) hab hw
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] at h
  exact h hA hB ht

/-- Input: any scale in the cell and any ordinate from 2.178 through 2.182.
Claim: the actual Gamma-resolvent gap is uniformly at least 533/8000000.
Proof: cover the band by the eight adjacent checked intervals.
Role: certify a continuous rectangle rather than isolated phase samples. -/
theorem phaseCell64_gap_on_band {x t : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) (ht : t ∈ Set.Icc (4356 / 2000 : ℝ) (4364 / 2000)) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  by_cases h0 : t ≤ (4357 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 0 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h0
    exact ⟨ht.1, h0⟩
  by_cases h1 : t ≤ (4358 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 1 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h0 h1
    exact ⟨(lt_of_not_ge h0).le, h1⟩
  by_cases h2 : t ≤ (4359 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 2 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h1 h2
    exact ⟨(lt_of_not_ge h1).le, h2⟩
  by_cases h3 : t ≤ (4360 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 3 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h2 h3
    exact ⟨(lt_of_not_ge h2).le, h3⟩
  by_cases h4 : t ≤ (4361 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 4 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h3 h4
    exact ⟨(lt_of_not_ge h3).le, h4⟩
  by_cases h5 : t ≤ (4362 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 5 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h4 h5
    exact ⟨(lt_of_not_ge h4).le, h5⟩
  by_cases h6 : t ≤ (4363 / 2000 : ℝ)
  · apply phaseCell64_gap_on_checked_interval hlo hhi 6 (by norm_num only)
    norm_num only [Nat.cast_ofNat]
    norm_num only at ht h5 h6
    exact ⟨(lt_of_not_ge h5).le, h6⟩
  apply phaseCell64_gap_on_checked_interval hlo hhi 7 (by norm_num only)
  norm_num only [Nat.cast_ofNat]
  norm_num only at ht h6
  exact ⟨(lt_of_not_ge h6).le, ht.2⟩

/-- Input: a real level between 64 and 64.001.
Claim: its Gamma scale L^2/(99/40) lies in the exact rational cell.
Proof: square both level inequalities while preserving nonnegativity.
Role: connect the spectral cell to the intended witness-analysis parameter. -/
theorem scale64_cell_of_level {L : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000) :
    (163840 / 99 : ℝ) ≤ L ^ 2 / (99 / 40) ∧ L ^ 2 / (99 / 40) ≤ (4096128001 / 2475000 : ℝ) := by
  have hL0 : 0 ≤ L := le_trans (by norm_num only) hlo
  have hA := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 64) hlo
  have hB := mul_self_le_mul_self hL0 hhi
  norm_num only at hA hB ⊢
  constructor <;> nlinarith only [hA, hB]

/-- Input: any real level in [64,64.001] and ordinate in [2.178,2.182].
Claim: the actual Gamma phase at scale L^2/(99/40) has uniform resolvent margin 533/8000000.
Proof: apply the scale inclusion to the continuous rectangle theorem.
Role: expose the certified spectral rectangle in witness-analysis coordinates. -/
theorem phaseCell64_gap_on_band_of_level {L t : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000)
    (ht : t ∈ Set.Icc (4356 / 2000 : ℝ) (4364 / 2000)) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
            ((L ^ 2 / (99 / 40) : ℝ) : ℂ) ^ (Complex.I * t)).re := by
  obtain ⟨ha, hb⟩ := scale64_cell_of_level hlo hhi
  exact phaseCell64_gap_on_band ha hb ht

/-- Input: a scale in the first cell and an ordinate whose absolute value is in [2.178,2.182].
Claim: the same positive phase gap holds in both symmetric ordinate bands.
Proof: use the positive-band certificate and the general evenness of the actual Gamma phase.
Role: reuse the certified nodes without recomputing negative ordinates. -/
theorem phaseCell64_gap_on_abs_band {x t : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) (ht : |t| ∈ Set.Icc (4356 / 2000 : ℝ) (4364 / 2000)) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have h := phaseCell64_gap_on_band hlo hhi ht
  have hR :
    finiteSignedResolvent phaseResolvent64Coefficients |t| =
      finiteSignedResolvent phaseResolvent64Coefficients t := by
    simp only [finiteSignedResolvent, sq_abs]
  rw [hR] at h
  by_cases ht0 : 0 ≤ t
  · simpa only [abs_of_nonneg ht0] using h
  · rw [abs_of_neg (lt_of_not_ge ht0),
      gammaHalf_phase_re_neg (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 163840 / 99) hlo)] at h
    exact h

/-- Input: a level in [64,64.001] and absolute ordinate in [2.178,2.182].
Claim: the actual Gamma phase at scale L^2/(99/40) has margin 533/8000000.
Proof: transport the scale cell and use the symmetric-band theorem.
Role: expose the two continuous spectral rectangles in witness-analysis coordinates. -/
theorem phaseCell64_gap_on_abs_band_of_level {L t : ℝ} (hlo : (64 : ℝ) ≤ L) (hhi : L ≤ 64001 / 1000)
    (ht : |t| ∈ Set.Icc (4356 / 2000 : ℝ) (4364 / 2000)) :
    (533 / 8000000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients t +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
            ((L ^ 2 / (99 / 40) : ℝ) : ℂ) ^ (Complex.I * t)).re := by
  obtain ⟨ha, hb⟩ := scale64_cell_of_level hlo hhi
  exact phaseCell64_gap_on_abs_band ha hb ht

end PseudoPrime.Analysis
