/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.XiEndpointNormBounds
public import PseudoPrime.LLS.LogLValueParityBounds
public import PseudoPrime.LLS.RiemannExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Numerical bounds for the completed logarithmic derivative

Rational logarithm bounds and the reciprocal explicit formula evaluate the
cutoff-100 arithmetic majorant in the endpoint estimate.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For natural levels at least eight, `log(q/pi)` is at least `93/100`.
Monotonicity bounds the numerator by eight; the tangent bound at three bounds
`log pi`. This controls the negative sign of the cutoff-100 correction. -/
theorem log_level_div_pi_ge_ninetyThree_hundredths {q : ℕ} (hq : 8 ≤ q) :
    (93 / 100 : ℝ) ≤ Real.log ((q : ℝ) / Real.pi) := by
  have hqc : (8 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num only) hqc
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hqc
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hlo
  norm_num only at hlo
  have hhi :=
    Analysis.log_le_log_add_sub_div (a := (3 : ℝ)) (y := Real.pi) (by norm_num only) Real.pi_pos
  rw [Real.log_div hq0.ne' Real.pi_ne_zero]
  nlinarith only [hlo, hhi, Real.pi_lt_d4, Real.log_two_gt_d9, Real.log_three_lt_d9]

/-- At cutoff `100`, either parity correction is nonpositive and is bounded
below by `-log 2 - gamma/2`. The parity-series estimates and rational logarithm
bounds prove both signs. These bounds retain the cancellation of the Euler constant
when the reciprocal arithmetic majorant is added. -/
theorem reciprocalCorrection_hundred_bounds {q : ℕ} (χ : DirichletCharacter ℂ q) :
    -Real.log 2 - Real.eulerMascheroniConstant / 2 ≤ reciprocalCorrection χ 100 ∧
      reciprocalCorrection χ 100 ≤ 0 := by
  by_cases he : χ (-1) = 1
  · rw [reciprocalCorrection, ite_eq_left he]
    have h := reciprocalCorrectionEven_bounds 100 le_rfl
    refine ⟨h.1, ?_⟩
    nlinarith only [h.2, Analysis.log_hundred_le_fourHundredSixtyThree_hundredths,
      Real.log_two_gt_d9, Real.one_half_lt_eulerMascheroniConstant,
      Real.eulerMascheroniConstant_lt_two_thirds]
  · rw [reciprocalCorrection, ite_eq_right he]
    have h := reciprocalCorrectionOdd_bounds 100 le_rfl
    constructor
    · linarith only [h.1, Real.log_two_gt_d9]
    · nlinarith only [h.2, Real.log_two_lt_d9, Real.one_half_lt_eulerMascheroniConstant,
        Real.eulerMascheroniConstant_lt_two_thirds]

/-- Under RH, the cutoff-100 majorant for any character is bounded by the maximum
of two affine functions of `log(q/pi)`. The parity bounds and the real reciprocal
explicit formula control the two signs separately, preserving Euler-constant
cancellation. This also handles the small primitive levels in the coset estimate. -/
theorem reciprocal_cutoff_hundred_majorant_le_max {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum 100 +
        |(99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ 100| ≤
      max ((789 / 250 : ℝ) + (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi))
        ((41 / 10 : ℝ) - (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi)) := by
  have hs := reciprocalWeightedMangoldtSum_le_explicit hRH (by norm_num only : (1 : ℝ) < 100)
  norm_num only at hs
  have he := reciprocalCorrection_hundred_bounds χ
  have hpi :=
    Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos)
      (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num only : (0 : ℝ) ≤ 2))
  rw [show (2 : ℝ) * 4 = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hpi
  norm_num only at hpi
  rw [add_comm, ← le_sub_iff_add_le, abs_le]
  constructor <;>
    nlinarith only [hs, he.1, he.2, hpi,
      le_max_left ((789 / 250 : ℝ) + (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi))
        ((41 / 10 : ℝ) - (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi)),
      le_max_right ((789 / 250 : ℝ) + (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi))
        ((41 / 10 : ℝ) - (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi)),
      Analysis.log_hundred_le_fourHundredSixtyThree_hundredths,
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth, Real.log_two_lt_d9,
      Real.one_half_lt_eulerMascheroniConstant]

/-- Under RH, for a character of level at least eight, the cutoff-100 reciprocal
majorant and parity correction are at most `79/100` times the endpoint bound.
The real reciprocal explicit formula retains the Euler-constant cancellation
in the negative branch of the absolute value. This evaluates the endpoint estimate. -/
theorem reciprocal_cutoff_hundred_majorant_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 8 ≤ q)
    (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum 100 +
        |(99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ 100| ≤
      (79 / 100 : ℝ) * ((2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4) := by
  have hm := reciprocal_cutoff_hundred_majorant_le_max χ hRH
  have hL := log_level_div_pi_ge_ninetyThree_hundredths hq
  apply hm.trans
  apply max_le <;> nlinarith only [hL]

/-- For a primitive character of level at least eight, GRH bounds the norm
of the logarithmic derivative of xi at zero by
`(2/3) log(q/pi) + 4`. Apply the cutoff-100 estimate and its rational majorant.
This is the endpoint estimate used in the logarithmic coset comparison. -/
theorem norm_logDeriv_xi_zero_le_log_level {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 8 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv (xi χ) 0‖ ≤ (2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4 := by
  have hb := norm_logDeriv_xi_zero_le_cutoff100 ((by norm_num only : 3 ≤ 8).trans hq) hp hGRH
  have hm := reciprocal_cutoff_hundred_majorant_le χ hq hGRH.riemann
  nlinarith only [hb, hm]

/-- At natural levels from three through seven, `log(q/pi)` lies in `[-1/20,1]`.
The tangent bound at three controls the lower endpoint; comparison with eight
and three controls the upper endpoint. This treats small primitive conductors. -/
theorem log_level_div_pi_small_bounds {q : ℕ} (hq : 3 ≤ q) (hq8 : q < 8) :
    -(1 / 20 : ℝ) ≤ Real.log ((q : ℝ) / Real.pi) ∧ Real.log ((q : ℝ) / Real.pi) ≤ 1 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq8' : (q : ℝ) ≤ 8 := by exact_mod_cast hq8.le
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num only) hq3
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hq3
  have hhi := Real.log_le_log hq0 hq8'
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hhi
  norm_num only at hhi
  have hpiHi :=
    Analysis.log_le_log_add_sub_div (a := (3 : ℝ)) (y := Real.pi) (by norm_num only) Real.pi_pos
  have hpiLo := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) Real.pi_gt_three.le
  rw [Real.log_div hq0.ne' Real.pi_ne_zero]
  constructor <;>
    nlinarith only [hlo, hhi, hpiHi, hpiLo, Real.pi_lt_d4, Real.log_two_lt_d9, Real.log_three_gt_d9]

/-- Under GRH, the endpoint logarithmic derivative has norm at most six for
primitive characters of levels three through seven. The logarithmic interval
bounds both affine branches of the cutoff-100 majorant by `9/2`.
This supplies the small-conductor case without character enumeration. -/
theorem norm_logDeriv_xi_zero_le_six_of_small_level {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hq8 : q < 8) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) : ‖logDeriv (xi χ) 0‖ ≤ 6 := by
  have hb := norm_logDeriv_xi_zero_le_cutoff100 hq hp hGRH
  have hm := reciprocal_cutoff_hundred_majorant_le_max χ hGRH.riemann
  have hL := log_level_div_pi_small_bounds hq hq8
  have hm' :
    max ((789 / 250 : ℝ) + (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi))
        ((41 / 10 : ℝ) - (99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi)) ≤
      9 / 2 := by
    apply max_le <;> nlinarith only [hL.1, hL.2]
  nlinarith only [hb, hm, hm']

/-- Under GRH, a primitive character of conductor at least three and at most
the ambient modulus has endpoint norm at most `(2/3) log(q/pi) + 4` when
`log(q/pi) ≥ 3`. Larger conductors use the sharp endpoint estimate; smaller
conductors use the uniform bound six. The explicit logarithmic condition
allows the coset argument to use a smaller modulus threshold. -/
theorem norm_logDeriv_xi_zero_le_log_ambient_of_log_lower_bound {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hL : 3 ≤ Real.log ((q : ℝ) / Real.pi)) (hm : 3 ≤ m) (hmq : m ≤ q)
    (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv (xi χ) 0‖ ≤ (2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4 := by
  by_cases hm8 : 8 ≤ m
  · have hb := norm_logDeriv_xi_zero_le_log_level hm8 hp hGRH
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 3) hm)
    have hl :=
      Real.log_le_log (div_pos hm0 Real.pi_pos)
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr hmq) Real.pi_pos.le)
    nlinarith only [hb, hl]
  · have hb := norm_logDeriv_xi_zero_le_six_of_small_level hm (Nat.lt_of_not_ge hm8) hp hGRH
    nlinarith only [hb, hL]

/-- Under GRH, a primitive character of level `m ≥ 3` has endpoint norm at most
`(2/3) log(q/pi) + 4` whenever `m ≤ q` and `q ≥ 20000`.
For `m ≥ 8`, enlarge the logarithm in the sharp estimate; smaller conductors
use the uniform bound six. This proves the endpoint input of equation (4.6)
with the ambient modulus used in Theorem 1.4. -/
theorem norm_logDeriv_xi_zero_le_log_ambient_level {q m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv (xi χ) 0‖ ≤ (2 / 3 : ℝ) * Real.log ((q : ℝ) / Real.pi) + 4 := by
  apply norm_logDeriv_xi_zero_le_log_ambient_of_log_lower_bound ?_ hm hmq hp hGRH
  have hl := Analysis.eight_lt_log_level ((by decide : 3000 ≤ 20000).trans hq)
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 20000) hq)
  have hpi := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
  rw [Real.log_four_eq] at hpi
  rw [Real.log_div hq0.ne' Real.pi_ne_zero]
  nlinarith only [hl, hpi, Real.log_two_lt_d9]

end PseudoPrime.LLS.PaperStatements
