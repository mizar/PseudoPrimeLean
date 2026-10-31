/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialTaylorCertificates
public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import PseudoPrime.Analysis.ExponentialRampCutoff
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational lower certificates for exponential ramp atoms -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The rational factor multiplying exp(-t) in the ramp weight.
Its three branches match the actual ramp before, during and after
the two joins. This avoids a floating-point branch decision in certificates. -/
def gammaRationalRampFactor (t : ℚ) : ℚ :=
  if t ≤ 247 / 100 then 1 else if t ≤ 99 / 40 then (99 / 40 - t) / (1 / 200) else 0

/-- The rational ramp factor is nonnegative at every height.
Check its branches and the nonnegative linear numerator on the middle
interval. This permits multiplication of the exponential lower bound. -/
theorem gamma_rational_ramp_factor_nonneg (t : ℚ) : 0 ≤ gammaRationalRampFactor t := by
  by_cases hl : t ≤ 247 / 100
  · rw [gammaRationalRampFactor, ite_eq_left hl]
    norm_num only
  · by_cases hr : t ≤ 99 / 40
    · rw [gammaRationalRampFactor, ite_eq_right hl, ite_eq_left hr]
      exact div_nonneg (sub_nonneg.mpr hr) (by norm_num only)
    · rw [gammaRationalRampFactor, ite_eq_right hl, ite_eq_right hr]

/-- At a rational height the actual ramp is exp(-t) times the exact
rational factor. Transfer the two rational comparisons to the reals
and identify each branch. This includes both endpoints of the joins. -/
theorem exponentialRampWeight_eq_rational_factor (t : ℚ) :
    Analysis.exponentialRampWeight (t : ℝ) =
      Real.exp (-(t : ℝ)) * (gammaRationalRampFactor t : ℝ) := by
  have hleft : (t : ℝ) ≤ 247 / 100 ↔ t ≤ (247 / 100 : ℚ) := by
    have h := Rat.cast_le (K := ℝ) (p := t) (q := (247 / 100 : ℚ))
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have hright : (t : ℝ) ≤ 99 / 40 ↔ t ≤ (99 / 40 : ℚ) := by
    have h := Rat.cast_le (K := ℝ) (p := t) (q := (99 / 40 : ℚ))
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  by_cases hl : t ≤ 247 / 100
  · rw [Analysis.exponentialRampWeight_eq_exp_of_le_left (hleft.mpr hl), gammaRationalRampFactor,
      ite_eq_left hl, Rat.cast_one, mul_one]
  · by_cases hr : t ≤ 99 / 40
    · rw [Analysis.exponentialRampWeight_eq_middle (le_of_not_ge (hleft.not.mpr hl))
          (hright.mpr hr),
        gammaRationalRampFactor, ite_eq_right hl, ite_eq_left hr]
      norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
      ring
    · rw [Analysis.exponentialRampWeight_eq_zero (le_of_not_ge (hright.not.mpr hr)),
        gammaRationalRampFactor, ite_eq_right hl, ite_eq_right hr, Rat.cast_zero, mul_zero]

/-- A finite rational check for a lower ramp value at height t.
It records the nonnegative height, Taylor tail condition and proposed
nonnegative lower endpoint. Primality and support are separate checks. -/
def gammaRationalRampLowerCheck (t : ℚ) (n : ℕ) (l : ℚ) : Bool :=
  decide
    (0 ≤ t ∧
      t / (n + 1 : ℕ) ≤ 1 / 2 ∧
      0 ≤ l ∧ l ≤ Analysis.gammaExpTaylorLower t n * gammaRationalRampFactor t)

/-- A successful rational ramp check implies the proposed nonnegative
lower endpoint bounds the actual ramp weight. Combine the reciprocal
Taylor estimate, the exact factor identity and the recorded comparison.
This reflects executable rational arithmetic into the analytic row bound. -/
theorem gamma_rational_ramp_lower_check_sound {t l : ℚ} {n : ℕ}
    (hc : gammaRationalRampLowerCheck t n l = true) :
    0 ≤ (l : ℝ) ∧ (l : ℝ) ≤ Analysis.exponentialRampWeight (t : ℝ) := by
  obtain ⟨ht, hs, hl0, hl⟩ := of_decide_eq_true hc
  have hb :=
    mul_le_mul_of_nonneg_right (Analysis.gamma_exp_taylor_lower_valid ht hs)
      ((Rat.cast_nonneg (K := ℝ)).mpr (gamma_rational_ramp_factor_nonneg t))
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  rw [Rat.cast_mul] at hlR
  rw [← exponentialRampWeight_eq_rational_factor] at hb
  exact ⟨(Rat.cast_nonneg (K := ℝ)).mpr hl0, hlR.trans hb⟩

end PseudoPrime.LLS
