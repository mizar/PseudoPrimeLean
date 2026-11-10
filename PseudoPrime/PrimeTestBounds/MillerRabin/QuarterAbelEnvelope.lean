/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028BudgetGeneral

/-! # Rational endpoint envelope for quarter-square cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An explicit upper envelope for a quarter-cell budget. The arguments bound the
logarithm, negative power and square root of the cutoff and the Euler prefix. -/
noncomputable def quarterAbelEnvelope (U L Q s t P : ℝ) : ℝ :=
  (2 * U) * (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * Q * ((21 / 8 : ℝ) + L) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * Q) *
          quarterMomentPolynomial ((21 / 8 : ℝ) + L) +
        (3 / 8 : ℝ) * U +
        (77 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
      4 * P +
    t * (35091 / 100000 : ℝ) +
    ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
      ((1839 / 1000 : ℝ) * (L + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) / s)

/-- Endpoint bounds and six moment estimates control the quarter-cell budget.
The proof compares each nonnegative factor separately. -/
theorem quarter_abel_envelope {X U L Q s t P : ℝ} (hX : 1 ≤ X) (hU : 0 ≤ U) (hlog : Real.log X ≤ L)
    (hpow : X ^ (-(27 / 25 : ℝ)) ≤ Q) (hs : 0 < s) (hsqrt : s ≤ Real.sqrt X)
    (hsqrtU : Real.sqrt X ≤ t) (hm : QuarterMomentBounds) :
    quarterUniformBudget X U P (quarterUniformAbel X)
        (refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X) ≤
      quarterAbelEnvelope U L Q s t P := by
  let z : ℝ := (21 / 8 : ℝ) + Real.log X
  let Z : ℝ := (21 / 8 : ℝ) + L
  let E : ℝ := Real.exp (-((27 / 25 : ℝ) * (21 / 8)))
  let V : ℝ := X ^ (-(27 / 25 : ℝ))
  let R : ℝ := Real.sqrt X
  let F : ℝ := (refinedSixPoleKernel.function (1 / 2)).re
  have hl0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hz0 : 0 ≤ z := by
    dsimp only [z]; linarith only [hl0]
  have hz : z ≤ Z := by
    dsimp only [z, Z]; linarith only [hlog]
  have he : E ≤ (588 / 10000 : ℝ) := by
    dsimp only [E]
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hQ0 : 0 ≤ V := Real.rpow_nonneg (by linarith only [hX]) _
  have hP0 : 0 ≤ Q := hQ0.trans hpow
  have hep := mul_le_mul he hpow hQ0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hep0 : 0 ≤ (588 / 10000 : ℝ) * Q := mul_nonneg (by norm_num only) hP0
  have hZpow := pow_le_pow_left₀ hz0 hz 5
  have hepz := mul_le_mul hep hZpow (pow_nonneg hz0 5) hep0
  have hpoly0 : 0 ≤ quarterMomentPolynomial z := by
    dsimp only [quarterMomentPolynomial]
    positivity
  have hpoly := quarter_moment_polynomial_le hz0 hz
  have hepoly := mul_le_mul hep hpoly hpoly0 hep0
  have hf0 : 0 ≤ F := by
    dsimp only [F]
    rw [refined_six_pole_half]
    positivity
  have hf : F ≤ (35091 / 100000 : ℝ) := refined_six_pole_half_upper
  have ht0 : 0 ≤ t := (Real.sqrt_nonneg X).trans hsqrtU
  have hRF := mul_le_mul hsqrtU hf hf0 ht0
  have hinv : R⁻¹ ≤ s⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hs hsqrt
  have hlinear : (1839 / 1000 : ℝ) * z + 2 ≤ (1839 / 1000 : ℝ) * Z + 2 := by
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hz (by norm_num only : (0 : ℝ) ≤ 1839 / 1000)) 2
  have hinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hlinearZ0 : 0 ≤ (1839 / 1000 : ℝ) * Z + 2 := by
    have hZ0 := hz0.trans hz
    positivity
  have herr := mul_le_mul hlinear hinv hinv0 hlinearZ0
  have hfirst :=
    mul_le_mul_of_nonneg_left hepz (show (0 : ℝ) ≤ 2 * U * ((27 / 25 : ℝ) ^ 5 / 120) by positivity)
  have hsecond :=
    mul_le_mul_of_nonneg_left hepoly (show (0 : ℝ) ≤ ((27 / 25 : ℝ) ^ 5 / 120) by positivity)
  have hlast :=
    mul_le_mul_of_nonneg_left herr
      (show (0 : ℝ) ≤ ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) by positivity)
  have hreflect := quarter_reflected_of_moments hX hm
  dsimp only [quarterUniformBudget, quarterUniformAbel, quarterAbelEnvelope]
  simp only [div_eq_mul_inv] at hlast ⊢
  dsimp only [z, Z, E, V, R, F] at hfirst hsecond hRF hlast
  simp only [div_eq_mul_inv] at hlast
  nlinarith only [hfirst, hsecond, hRF, hlast, hreflect]

end PseudoPrime.PrimeTestBounds.MillerRabin
