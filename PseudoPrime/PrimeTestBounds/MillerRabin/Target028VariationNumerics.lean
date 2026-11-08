/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028VariationSigns
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSharpError
public import PseudoPrime.Analysis.PreciseLogTaylorBounds

/-! # Rational endpoint bounds for the signed variation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational bounds for `sqrt 5` used at the two variation roots. Squaring
the positive rational endpoints checks both inequalities. -/
theorem target028_sqrt_five_bounds :
    (223606 / 100000 : ℝ) ≤ Real.sqrt 5 ∧ Real.sqrt 5 ≤ 223607 / 100000 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num only)
  · apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only

set_option maxRecDepth 8192 in
/-- The first negative exponential is below `194/1000000`. A rational
logarithm enclosure bounds the logarithm of the reciprocal. -/
theorem target028_exp_first : Real.exp (-(854856 / 100000 : ℝ)) ≤ 194 / 1000000 := by
  have h :=
    (Analysis.preciseLogCheck_sound
        (show Analysis.preciseLogCheck (500000 / 97) 13 64 8 (854856 / 100000) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (by norm_num only : (0 : ℝ) < 500000 / 97)] at he
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 500000 / 97) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi ⊢
  exact hi

set_option maxRecDepth 8192 in
/-- The second negative exponential is below `1697/100000`. A rational
logarithm enclosure bounds the logarithm of the reciprocal. -/
theorem target028_exp_second : Real.exp (-(407643 / 100000 : ℝ)) ≤ 1697 / 100000 := by
  have h :=
    (Analysis.preciseLogCheck_sound
        (show Analysis.preciseLogCheck (100000 / 1697) 6 64 4 (407643 / 100000) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (by norm_num only : (0 : ℝ) < 100000 / 1697)] at he
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 100000 / 1697) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi ⊢
  exact hi

set_option maxRecDepth 8192 in
/-- The first square-root primitive exponential is below `141/100000000`. A rational
logarithm enclosure bounds the logarithm of the reciprocal. -/
theorem target028_sqrt_exp_first : Real.exp (-(6737 / 500 : ℝ)) ≤ 141 / 100000000 := by
  have h :=
    (Analysis.preciseLogCheck_sound
        (show Analysis.preciseLogCheck (100000000 / 141) 20 64 13 (6737 / 500) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (by norm_num only : (0 : ℝ) < 100000000 / 141)] at he
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 100000000 / 141) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi ⊢
  exact hi

set_option maxRecDepth 8192 in
/-- The second square-root primitive exponential is below `583/100000`. A rational
logarithm enclosure bounds the logarithm of the reciprocal. -/
theorem target028_sqrt_exp_second : Real.exp (-(2573 / 500 : ℝ)) ≤ 583 / 100000 := by
  have h :=
    (Analysis.preciseLogCheck_sound
        (show Analysis.preciseLogCheck (100000 / 583) 8 64 5 (2573 / 500) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (by norm_num only : (0 : ℝ) < 100000 / 583)] at he
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 100000 / 583) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi ⊢
  exact hi

/-- The unweighted absolute second variation is at most `251/500` times the
kernel normalization `(27/25)^5`. Exact root and logarithm certificates
bound the two terms of the signed endpoint formula. -/
theorem target028_unweighted_variation_bound :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) ≤
      (251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hs := target028_sqrt_five_bounds
  have hplus0 : (0 : ℝ) ≤ 5 + Real.sqrt 5 := by linarith only [hs.1]
  have hminus0 : (0 : ℝ) ≤ 5 - Real.sqrt 5 := by linarith only [hs.2]
  have hp :=
    pow_le_pow_left₀ hplus0 (show 5 + Real.sqrt 5 ≤ (723607 / 100000 : ℝ) by linarith only [hs.2]) 4
  have hm :=
    pow_le_pow_left₀ hminus0 (show 5 - Real.sqrt 5 ≤ (276394 / 100000 : ℝ) by linarith only [hs.1])
      4
  have he1 : Real.exp (-(21 / 16 : ℝ) - (5 + Real.sqrt 5)) ≤ 194 / 1000000 :=
    (Real.exp_le_exp.mpr (by linarith only [hs.1])).trans target028_exp_first
  have he2 : Real.exp (-(21 / 16 : ℝ) - (5 - Real.sqrt 5)) ≤ 1697 / 100000 :=
    (Real.exp_le_exp.mpr (by linarith only [hs.2])).trans target028_exp_second
  have ht1 :=
    mul_le_mul hp he1 (Real.exp_nonneg _) (by norm_num only : (0 : ℝ) ≤ (723607 / 100000 : ℝ) ^ 4)
  have ht2 :=
    mul_le_mul hm he2 (Real.exp_nonneg _) (by norm_num only : (0 : ℝ) ≤ (276394 / 100000 : ℝ) ^ 4)
  have hsum :
    (5 + Real.sqrt 5) ^ 4 * Real.exp (-(21 / 16 : ℝ) - (5 + Real.sqrt 5)) +
        (5 - Real.sqrt 5) ^ 4 * Real.exp (-(21 / 16 : ℝ) - (5 - Real.sqrt 5)) ≤
      (723607 / 100000 : ℝ) ^ 4 * (194 / 1000000) + (276394 / 100000 : ℝ) ^ 4 * (1697 / 100000) :=
    add_le_add ht1 ht2
  have hsum0 :
    0 ≤
      (5 + Real.sqrt 5) ^ 4 * Real.exp (-(21 / 16 : ℝ) - (5 + Real.sqrt 5)) +
        (5 - Real.sqrt 5) ^ 4 * Real.exp (-(21 / 16 : ℝ) - (5 - Real.sqrt 5)) :=
    add_nonneg (mul_nonneg (pow_nonneg hplus0 _) (Real.exp_nonneg _))
      (mul_nonneg (pow_nonneg hminus0 _) (Real.exp_nonneg _))
  have hprod := mul_le_mul hs.2 hsum hsum0 (by norm_num only : (0 : ℝ) ≤ 223607 / 100000)
  rw [target028_variation_explicit]
  have hfactor : (0 : ℝ) ≤ 2 * ((27 / 25 : ℝ) * (54 / 29 : ℝ) ^ 4 / 120) := by norm_num only
  have hbound := mul_le_mul_of_nonneg_left hprod hfactor
  have hrat :
    2 * ((27 / 25 : ℝ) * (54 / 29 : ℝ) ^ 4 / 120) * (223607 / 100000) *
        ((723607 / 100000 : ℝ) ^ 4 * (194 / 1000000) +
          (276394 / 100000 : ℝ) ^ 4 * (1697 / 100000)) ≤
      (251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    norm_num only
  nlinarith only [hbound, hrat]

/-- Under RH, the principal-sum error integral admits the sharper unweighted
variation allowance from the exact sign split. The square-root-weighted
variation still uses its existing majorant until its endpoint bound is proved. -/
theorem target028_sharp_integral_unweighted (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u| ≤
      (231 / 5000 : ℝ) * Real.sqrt x * (6889 / 2700) +
        ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
          ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) := by
  have h := refined_sharp_integral_bound hRH hx hy hyb
  have hc : 0 ≤ (1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2 := by
    linarith only [Real.log_nonneg hx]
  have hV :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), |refinedSecondDensity u|) ≤
      (251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    rw [← intervalIntegral.integral_of_le (Real.exp_pos _).le]
    exact target028_unweighted_variation_bound
  exact h.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hV hc))

/-- At either quadratic root, the square-root-weighted primitive reduces to
a linear expression in the signed square root times one exponential. -/
theorem target028_primitive_at_root (s : ℝ) (hs : s ^ 2 = 5) :
    target028SqrtPrimitive (target028VariationPoint (5 + s)) =
      Real.exp (-((54 / 29 : ℝ) * (5 + s))) * ((11361114 * s + 22822655) / 454140) := by
  dsimp only [target028SqrtPrimitive]
  rw [target028_coord_at_point]
  congr 1
  linear_combination (27 * (13122 * s ^ 3 + 232065 * s ^ 2 + 1482660 * s + 4099450) / 6097250) * hs

/-- The square-root-weighted absolute second variation is at most `203/1000`
times the kernel normalization `(27/25)^5`. Certified root and exponential
enclosures bound both endpoint values of the exact primitive. -/
theorem target028_sqrt_variation_bound :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * |refinedSecondDensity u|) ≤
      (203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hs := target028_sqrt_five_bounds
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num only)
  have hp0 : (0 : ℝ) ≤ (11361114 * Real.sqrt 5 + 22822655) / 454140 := by linarith only [hs.1]
  have hp : (11361114 * Real.sqrt 5 + 22822655) / 454140 ≤ (107 : ℝ) := by linarith only [hs.2]
  have hm0 : (0 : ℝ) ≤ (11361114 * Real.sqrt 5 - 22822655) / 454140 := by linarith only [hs.1]
  have hm : (11361114 * Real.sqrt 5 - 22822655) / 454140 ≤ (569 / 100 : ℝ) := by
    linarith only [hs.2]
  have he1 : Real.exp (-((54 / 29 : ℝ) * (5 + Real.sqrt 5))) ≤ 141 / 100000000 :=
    (Real.exp_le_exp.mpr (by linarith only [hs.1])).trans target028_sqrt_exp_first
  have he2 : Real.exp (-((54 / 29 : ℝ) * (5 - Real.sqrt 5))) ≤ 583 / 100000 :=
    (Real.exp_le_exp.mpr (by linarith only [hs.2])).trans target028_sqrt_exp_second
  have hplus := mul_le_mul he1 hp hp0 (by norm_num only : (0 : ℝ) ≤ 141 / 100000000)
  have hminus := mul_le_mul he2 hm hm0 (by norm_num only : (0 : ℝ) ≤ 583 / 100000)
  have hroot1 := target028_primitive_at_root (Real.sqrt 5) hs2
  have hroot2 := target028_primitive_at_root (-Real.sqrt 5) (by nlinarith only [hs2])
  rw [target028_sqrt_variation_eq_primitive]
  change
    (25 / 108 : ℝ) +
        2 *
          (target028SqrtPrimitive (target028VariationPoint (5 + Real.sqrt 5)) -
            target028SqrtPrimitive (target028VariationPoint (5 + -Real.sqrt 5))) ≤
      _
  rw [hroot1, hroot2]
  have hrat :
    (25 / 108 : ℝ) + 2 * ((141 / 100000000 : ℝ) * 107 + (583 / 100000 : ℝ) * (569 / 100)) ≤
      (203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    norm_num only
  rw [show (5 : ℝ) + -Real.sqrt 5 = 5 - Real.sqrt 5 by ring]
  nlinarith only [hplus, hminus, hrat]

end PseudoPrime.PrimeTestBounds.MillerRabin
