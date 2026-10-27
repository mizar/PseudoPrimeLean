/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEulerTailErrorBounds
public import PseudoPrime.Analysis.GammaSmallPrimeCosts

/-! # Rational certification of the Gamma Euler tail error at cutoff 50000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Rational upper endpoints for the two cutoff powers at every fixed Gamma node.
The certificate uses integer twentieth powers at cutoff 50000. -/
def gammaTailRatioUpper (a : ℚ) : ℚ × ℚ :=
  if a = 11 / 20 then (65089 / 25000000, 233 / 20000000)
  else
    if a = 13 / 20 then (88241 / 100000000, 79 / 20000000)
    else
      if a = 4 / 5 then (4353 / 25000000, 39 / 50000000)
      else
        if a = 1 then (1 / 50000, 9 / 100000000)
        else
          if a = 13 / 10 then (39 / 50000000, 1 / 100000000)
          else
            if a = 17 / 10 then (1 / 50000000, 1 / 100000000)
            else
              if a = 23 / 10 then (1 / 100000000, 1 / 100000000)
              else
                if a = 16 / 5 then (1 / 100000000, 1 / 100000000)
                else
                  if a = 9 / 2 then (1 / 100000000, 1 / 100000000)
                  else if a = 7 then (1 / 100000000, 1 / 100000000) else (0, 0)

/-- Natural exponent twenty times the rational Gamma node.
Its exact equality is certified for the fixed coefficient list below. -/
def gammaTailHalfPowerExponent (a : ℚ) : ℕ :=
  (20 * a).num.toNat

/-- Natural exponent twenty times the shifted Gamma node.
Its exact equality certifies the second cutoff power. -/
def gammaTailFullPowerExponent (a : ℚ) : ℕ :=
  (20 * a + 10).num.toNat

/-- Rational scalar error allowance using the certified power endpoints
and log cutoff at most twelve. This bounds one real scalar RH error budget. -/
def gammaTailNodeRationalBudget (a : ℚ) : ℚ :=
  let σ := (1 / 2 : ℚ) + a
  let uv := gammaTailRatioUpper a
  (1 / 20 : ℚ) * (σ ^ 2 * uv.1 / (σ - 1 / 2)) + (1839 / 1000 : ℚ) * (uv.2 * (1 + σ * 12)) +
    (21 / 20 : ℚ) * (σ * uv.2)

/-- Every fixed Gamma node has nonnegative endpoints, exact exponent
identities and valid integer twentieth-power upper checks. Kernel finite
arithmetic certifies the data for the later real-power bounds. -/
theorem gamma_tail_ratio_upper_checks :
    Analysis.gammaResolventCoefficients.Forall
      (fun ab ↦
        let uv := gammaTailRatioUpper ab.1
        0 ≤ uv.1 ∧
          0 ≤ uv.2 ∧
          20 * ab.1 = (gammaTailHalfPowerExponent ab.1 : ℚ) ∧
          20 * ab.1 + 10 = (gammaTailFullPowerExponent ab.1 : ℚ) ∧
          1 ≤ uv.1 ^ 20 * (50000 : ℚ) ^ gammaTailHalfPowerExponent ab.1 ∧
          1 ≤ uv.2 ^ 20 * (50000 : ℚ) ^ gammaTailFullPowerExponent ab.1) := by
  decide +kernel

/-- The fixed rational coefficient-weighted allowances sum to at most
one over 2500. Exact kernel arithmetic checks this finite numerical input. -/
theorem gamma_tail_rational_budget_check :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ |ab.2| * gammaTailNodeRationalBudget ab.1)).sum ≤
      (1 / 2500 : ℚ) := by
  decide +kernel

/-- The logarithm of cutoff 50000 is at most twelve. Compare with
2 to the sixteenth power and the certified upper bound for log two. -/
theorem gamma_tail_log_cutoff_le : Real.log (50000 : ℝ) ≤ 12 := by
  have he := Real.log_pow (2 : ℝ) 16
  norm_num only [Nat.cast_ofNat] at he
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 50000) (by norm_num only : (50000 : ℝ) ≤ 65536)
  linarith only [hm, he, Real.log_two_lt_d9]

/-- For every fixed Gamma node, the actual two real cutoff powers
lie below the rational endpoints. Cast the finite integer checks and apply
the proved twentieth-root interval theorem. -/
theorem gamma_tail_ratio_upper_valid (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    (50000 : ℝ) ^ (-(ab.1 : ℝ)) ≤ (gammaTailRatioUpper ab.1).1 ∧
      (50000 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (gammaTailRatioUpper ab.1).2 := by
  obtain ⟨hu, hv, he, hf, hhi, hfi⟩ :=
    List.forall_iff_forall_mem.mp gamma_tail_ratio_upper_checks ab hab
  have huR := (Rat.cast_le (K := ℝ)).mpr hu
  have hvR := (Rat.cast_le (K := ℝ)).mpr hv
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  have hfiR := (Rat.cast_le (K := ℝ)).mpr hfi
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  have hfR := congrArg (fun q : ℚ ↦ (q : ℝ)) hf
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one, Rat.cast_zero] at huR hvR hhiR hfiR heR hfR
  have hexp : -(gammaTailHalfPowerExponent ab.1 : ℝ) / 20 = -(ab.1 : ℝ) := by linarith only [heR]
  have hfexp : -(gammaTailFullPowerExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [hfR]
  constructor
  · simpa only [hexp] using
      (Analysis.gamma_rpow_neg_twentieth_interval (by norm_num only : (0 : ℝ) < 50000)
          (le_refl (0 : ℝ)) huR (gammaTailHalfPowerExponent ab.1)
          (by norm_num only [zero_pow, zero_mul]) hhiR).2
  · simpa only [hfexp] using
      (Analysis.gamma_rpow_neg_twentieth_interval (by norm_num only : (0 : ℝ) < 50000)
          (le_refl (0 : ℝ)) hvR (gammaTailFullPowerExponent ab.1)
          (by norm_num only [zero_pow, zero_mul]) hfiR).2

/-- For each fixed Gamma node, the actual scalar error budget at
50000 is at most its rational allowance. Compare the two certified real
powers and the logarithm factor term by term; all multipliers are nonnegative. -/
theorem gamma_tail_node_budget_le (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    powerRiemannErrorBudget (1 / 2 + (ab.1 : ℝ)) 50000 ≤
      (gammaTailNodeRationalBudget ab.1 : ℝ) := by
  obtain ⟨hu, hv⟩ := gamma_tail_ratio_upper_valid ab hab
  have hs := gammaResolvent_real_exponents_gt_one ab hab
  have hs0 : 0 ≤ (1 / 2 : ℝ) + (ab.1 : ℝ) := (zero_lt_one.trans hs).le
  have hd : 0 ≤ (1 / 2 : ℝ) + (ab.1 : ℝ) - 1 / 2 := by linarith only [hs]
  have hv0 :=
    (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 50000) (-(1 / 2 + (ab.1 : ℝ)))).trans hv
  have hl0 : 0 ≤ 1 + ((1 / 2 : ℝ) + (ab.1 : ℝ)) * Real.log 50000 :=
    add_nonneg (by norm_num only)
      (mul_nonneg hs0 (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 50000)))
  have hl := add_le_add_right (mul_le_mul_of_nonneg_left gamma_tail_log_cutoff_le hs0) 1
  have h1 :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu (sq_nonneg ((1 / 2 : ℝ) + (ab.1 : ℝ)))) hd)
      (by norm_num only : (0 : ℝ) ≤ 1 / 20)
  have h2 :=
    mul_le_mul_of_nonneg_left (mul_le_mul hv hl hl0 hv0) (by norm_num only : (0 : ℝ) ≤ 1839 / 1000)
  have h3 :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hs0)
      (by norm_num only : (0 : ℝ) ≤ 21 / 20)
  dsimp only [powerRiemannErrorBudget, gammaTailNodeRationalBudget]
  norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one]
  rw [show (1 / 2 : ℝ) - (1 / 2 + (ab.1 : ℝ)) = -(ab.1 : ℝ) by ring]
  exact add_le_add (add_le_add h1 h2) h3

/-- The actual common Euler error budget at cutoff 50000 is at most
one over 2500. Sum the real node bounds and cast the kernel rational
certificate. This supplies the numerical input for the RH mass bounds. -/
theorem gamma_tail_error_budget_le : gammaEulerTailErrorBudget 50000 ≤ (1 / 2500 : ℝ) := by
  have hn :=
    List.sum_le_sum
      (fun ab hab ↦
        mul_le_mul_of_nonneg_left (gamma_tail_node_budget_le ab hab) (abs_nonneg (ab.2 : ℝ)))
  have hc := (Rat.cast_le (K := ℝ)).mpr gamma_tail_rational_budget_check
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul, Rat.cast_abs,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
  dsimp only [gammaEulerTailErrorBudget, gammaRealPowerList]
  rw [List.map_map]
  exact hn.trans hc

/-- Under RH, the actual signed Euler tail error at cutoff 50000
has magnitude at most one over 2500. Connect the proved integral bound
to the numerical certificate, without discarding the signed main terms. -/
theorem gammaEulerTailError_abs_le_50000 (hRH : RiemannHypothesis) :
    |gammaEulerTailError 50000| ≤ (1 / 2500 : ℝ) := by
  exact
    (gammaEulerTailError_abs_le_budget hRH (by norm_num only : (1 : ℝ) ≤ 50000)).trans
      gamma_tail_error_budget_le

/-- Under RH, the actual infinite Euler mass lies within one over
2500 of its finite center at cutoff 50000. The exact mass identity and
certified error reduce the remaining numerical obligation to finite quantities. -/
theorem gammaEulerMass_bounds_50000 (hRH : RiemannHypothesis) :
    gammaEulerMassCenter 50000 - 1 / 2500 ≤ (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ∧
      (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ≤
        gammaEulerMassCenter 50000 + 1 / 2500 := by
  have hm := gammaEulerMass_eq_center_add_error hRH (by norm_num only : (1 : ℝ) ≤ 50000)
  have he := abs_le.mp (gammaEulerTailError_abs_le_50000 hRH)
  constructor <;> linarith only [hm, he.1, he.2]

end PseudoPrime.LLS
