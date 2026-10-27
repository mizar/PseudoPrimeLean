/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogDerivativeNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds

/-! # Refined Euler allowance on the reflected Gamma line

Retain the zeta denominator to reduce the completed derivative constant from 283 to 28.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Claim: two to the power minus one sixteenth is at least fifteen sixteenths.
Proof: log two is at most one and exp v is at least one plus v.
Role: certify the denominator in the Euler ratio on the reflected line. -/
theorem two_rpow_neg_sixteenth_lower : (15 / 16 : ℝ) ≤ (2 : ℝ) ^ (-1 / 16 : ℝ) := by
  rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 2)]
  have hl := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  have he := Real.add_one_le_exp (Real.log 2 * (-1 / 16))
  linarith only [hl, he]

/-- Claim: the Euler-ratio allowance at gap one sixteenth is at most seventeen.
Proof: use the certified lower bound for its denominator and exact rational arithmetic.
Role: replace the old ordinary logarithmic-derivative allowance 272. -/
theorem euler_ratio_sixteenth_le_seventeen :
    (((1 / 16 : ℝ)⁻¹ ^ 2 + (1 / 16 + 1)⁻¹) / (1 + (2 : ℝ) ^ (-(1 / 16 : ℝ)) / (1 / 16))) ≤ 17 := by
  have hp : (15 / 16 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 16 : ℝ)) := by
    simpa only [neg_div] using two_rpow_neg_sixteenth_lower
  have hd : (0 : ℝ) < 1 + (2 : ℝ) ^ (-(1 / 16 : ℝ)) / (1 / 16) := by nlinarith only [hp]
  apply (div_le_iff₀ hd).mpr
  norm_num only
  nlinarith only [hp]

/-- Input: any character of nonzero modulus and any real height.
Claim: the ordinary derivative norm on real part seventeen sixteenths is at most seventeen.
Proof: specialize the uniform Euler-ratio theorem and its rational allowance.
Role: supply the improved right-line input to completed reflection. -/
theorem norm_logDeriv_seventeen_sixteenths_le_seventeen {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖logDeriv χ.LFunction (((17 / 16 : ℝ) : ℂ) + t * Complex.I)‖ ≤ 17 := by
  have h := norm_logDeriv_vertical_le_euler_ratio χ (by norm_num only : (0 : ℝ) < 1 / 16) t
  have he : (1 + 1 / 16 : ℝ) = 17 / 16 := by norm_num only
  rw [he] at h
  exact h.trans euler_ratio_sixteenth_le_seventeen

/-- Input: the existing regular or primitive reflection data.
Claim: the completed derivative uses constant twenty-eight on the fixed line.
Proof: retain the Euler denominator and reflect without changing conductor normalization.
Role: replace the coarse constant in the left Gamma integral. -/
theorem norm_logDeriv_completed_seventeen_sixteenths_le_refined {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤ 28 + |t| := by
  let s : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * t
  have hr : s.re = 17 / 16 := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, zero_add]
  have hr1 : 1 ≤ s.re := by
    rw [hr]; norm_num only
  have hp : 0 < s.re := zero_lt_one.trans_le hr1
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr1) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have ho := norm_logDeriv_seventeen_sixteenths_le_seventeen χ t
  rw [mul_comm (t : ℂ) Complex.I] at ho
  have hg := norm_logDeriv_gammaFactor_seventeen_sixteenths_le χ hr
  rw [hi] at hg
  have hc :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [he]; ring
  change ‖logDeriv χ.completedLFunction s‖ ≤ _
  rw [hc]
  have hn := norm_add_le (logDeriv χ.LFunction s) (logDeriv χ.gammaFactor s)
  nlinarith only [hn, ho, hg]

/-- Input: the existing regular or primitive reflection data.
Claim: the completed derivative uses constant twenty-eight on the fixed line.
Proof: retain the Euler denominator and reflect without changing conductor normalization.
Role: replace the coarse constant in the left Gamma integral. -/
theorem norm_logDeriv_completed_neg_one_sixteenth_le_refined {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((-1 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      ‖Complex.log (q : ℂ)‖ + 28 + |t| := by
  let s : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
  have hr : 1 ≤ s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only
  have he :=
    completedLFunction_logDeriv_functionalEquation_at hp hne
      (completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hs_eq : 1 - s = ((-1 / 16 : ℝ) : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [hs_eq] at he
  have hn := norm_add_le (Complex.log (q : ℂ)) (logDeriv χ⁻¹.completedLFunction s)
  rw [← he, norm_neg] at hn
  have hb := norm_logDeriv_completed_seventeen_sixteenths_le_refined hinv (-t)
  rw [abs_neg] at hb
  exact hn.trans (by linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
