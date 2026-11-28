/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseLog107
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational log and power enclosures for the four section 107 endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected coefficient can be evaluated with a single positive
exponential because the two opposite exponential factors cancel. -/
theorem phase_ref_coeff107_eq :
    phaseRefCoeff107 =
      4 * ((51 / 50 : ℝ) ^ 5 / 120) * ((91 / 200) * Real.exp ((51 / 50) * (1 / 5)) - 11 / 25) := by
  unfold phaseRefCoeff107
  rw [neg_mul, Real.exp_neg]
  have h := inv_mul_cancel₀ (Real.exp_pos ((51 / 50 : ℝ) * (1 / 5))).ne'
  linear_combination (norm := ring) (-4 * ((51 / 50 : ℝ) ^ 5 / 120) * (11 / 25)) * h

/-- The section 107 reflected coefficient lies in a tight rational interval
using the existing exponential certificate at the shift gap. -/
theorem phase_ref_coeff107_bounds : phaseRefCoeff107 ∈ Set.Icc 0.004341453 0.004341455 := by
  rw [phase_ref_coeff107_eq]
  exact ⟨by linarith only [exp_h.1], by linarith only [exp_h.2]⟩

/-- The reciprocal pole coefficient lies in a tight rational interval,
obtained from the exponential series at one tenth. -/
theorem phase_recip107_bounds : phaseRecip107 ∈ Set.Icc 10.52995361 10.52995364 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (1 / 10 : ℝ)) 12
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (1 / 10 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hu
  unfold phaseRecip107
  exact ⟨by linarith only [hl], by linarith only [hu]⟩

private theorem phase_power_box {N lo hi : ℚ} {p d : ℕ} (hN : 0 < (N : ℝ))
    (h : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck N lo hi p d = true) :
    Real.exp ((-(p : ℝ) / (d : ℝ)) * Real.log (N : ℝ)) ∈ Set.Icc (lo : ℝ) (hi : ℝ) := by
  rw [mul_comm, ← Real.rpow_def_of_pos hN]
  exact AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound h

/-- The logarithm at radius 300 is enclosed by an exact rational check. -/
theorem phase_log107_300 :
    Real.log 90000 ∈ Set.Icc (11407564939312 / 10 ^ 12) (11407564959313 / 10 ^ 12) := by
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound (N := 90000) (j := 16) (n := 48) (lo :=
      11407564939312 / 10 ^ 12) (hi := 11407564959313 / 10 ^ 12) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow, Nat.cast_ofNat] at *
  exact hlog

/-- Certified logarithm and exponential factors at radius 313 for the phase remainder. -/
theorem phase_box107_313 :
    Real.log 97969 ∈ Set.Icc (11492406369080 / 10 ^ 12) (11492406393081 / 10 ^ 12) ∧
      Real.exp (-(13 / 25) * Real.log 97969) ∈
        Set.Icc (253883156349754752 / 10 ^ 20) (253883156349778752 / 10 ^ 20) ∧
      Real.exp (-(51 / 50) * Real.log 97969) ∈
        Set.Icc (811128295035178 / 10 ^ 20) (811128295059179 / 10 ^ 20) ∧
      Real.exp (-(77 / 50) * Real.log 97969) ∈
        Set.Icc (2059318105511 / 10 ^ 20) (2059318129512 / 10 ^ 20) ∧
      Real.exp (-(51 / 25) * Real.log 97969) ∈
        Set.Icc (6579279110 / 10 ^ 20) (6579303111 / 10 ^ 20) := by
  have hlog :=
    Analysis.rationalLogIntervalCheck_sound (N := 97969) (j := 16) (n := 48) (lo :=
      11492406369080 / 10 ^ 12) (hi := 11492406393081 / 10 ^ 12) (by decide +kernel)
  have h0 :=
    phase_power_box (N := 97969) (p := 13) (d := 25) (lo := 253883156349754752 / 10 ^ 20) (hi :=
      253883156349778752 / 10 ^ 20) (by norm_num only) (by decide +kernel)
  have h1 :=
    phase_power_box (N := 97969) (p := 51) (d := 50) (lo := 811128295035178 / 10 ^ 20) (hi :=
      811128295059179 / 10 ^ 20) (by norm_num only) (by decide +kernel)
  have h2 :=
    phase_power_box (N := 97969) (p := 77) (d := 50) (lo := 2059318105511 / 10 ^ 20) (hi :=
      2059318129512 / 10 ^ 20) (by norm_num only) (by decide +kernel)
  have h3 :=
    phase_power_box (N := 97969) (p := 51) (d := 25) (lo := 6579279110 / 10 ^ 20) (hi :=
      6579303111 / 10 ^ 20) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow, Nat.cast_ofNat, neg_div] at *
  exact ⟨hlog, h0, h1, h2, h3⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
