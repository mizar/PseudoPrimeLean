/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.RationalResolventApproximation
public import PseudoPrime.Analysis.GammaSmallPrimeCosts
public import PseudoPrime.Analysis.GeometricRatioBounds

/-! # Rational dyadic intervals at the Gamma resolvent nodes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- Rational intervals for the dyadic ratios at all resolvent nodes.
Integer twentieth-power comparisons generated endpoints with denominator
one hundred million. The finite checks below validate the data in Lean. -/
def gammaDyadicRatioInterval (a : ℚ) : ℚ × ℚ :=
  if a = 11 / 20 then (48296816 / 100000000, 48296817 / 100000000)
  else
    if a = 13 / 20 then (45062523 / 100000000, 45062524 / 100000000)
    else
      if a = 16 / 20 then (40612619 / 100000000, 40612620 / 100000000)
      else
        if a = 20 / 20 then (35355339 / 100000000, 35355340 / 100000000)
        else
          if a = 26 / 20 then (28717458 / 100000000, 28717459 / 100000000)
          else
            if a = 34 / 20 then (21763764 / 100000000, 21763765 / 100000000)
            else
              if a = 46 / 20 then (14358729 / 100000000, 14358730 / 100000000)
              else
                if a = 64 / 20 then (7694652 / 100000000, 7694653 / 100000000)
                else
                  if a = 90 / 20 then (3125000 / 100000000, 3125001 / 100000000)
                  else if a = 140 / 20 then (552427 / 100000000, 552428 / 100000000) else (0, 0)

/-- Every dyadic interval is nonnegative, ordered and below one, and bounds
the reciprocal twentieth root by exact rational power inequalities.
The exponent identity reuses the already certified node exponent definition. -/
theorem gamma_dyadic_ratio_checks :
    gammaResolventCoefficients.Forall
      (fun ab ↦
        let lu := gammaDyadicRatioInterval ab.1
        0 ≤ lu.1 ∧
          lu.1 ≤ lu.2 ∧
          lu.2 < 1 ∧
          20 * ab.1 + 10 = (Analysis.gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
          lu.1 ^ 20 * 2 ^ Analysis.gammaSmallPrimeRatioExponent ab.1 ≤ 1 ∧
          1 ≤ lu.2 ^ 20 * 2 ^ Analysis.gammaSmallPrimeRatioExponent ab.1) := by
  decide +kernel

/-- The certified dyadic interval contains each actual real Euler ratio.
Cast the finite checks and apply the proved twentieth-root interval theorem.
This connects the rational data to both dyadic geometric cost formulas. -/
theorem gamma_dyadic_ratio_interval_valid (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) :
    (gammaDyadicRatioInterval ab.1).1 ≤ (2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (gammaDyadicRatioInterval ab.1).2 := by
  obtain ⟨hl, hlu, _, he, hlo, hhi⟩ :=
    List.forall_iff_forall_mem.mp gamma_dyadic_ratio_checks ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_le (K := ℝ)).mpr hlu
  have hloR := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhiR := (Rat.cast_le (K := ℝ)).mpr hhi
  have heR := congrArg (fun q : ℚ ↦ (q : ℝ)) he
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_one, Rat.cast_zero] at hlR huR hloR hhiR heR
  have hexp : -(Analysis.gammaSmallPrimeRatioExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  simpa only [hexp] using
    Analysis.gamma_rpow_neg_twentieth_interval (by norm_num only : (0 : ℝ) < 2) hlR (hlR.trans huR)
      (Analysis.gammaSmallPrimeRatioExponent ab.1) hloR hhiR

/-- A rational signed node allowance for the dyadic geometric denominator.
Exponent one represents all positive powers; exponent two represents odd powers.
Choose the ratio endpoint by the sign of the coefficient to preserve cancellation. -/
def gammaDyadicNodeUpper (j : ℕ) (ab : ℚ × ℚ) : ℚ :=
  let lu := gammaDyadicRatioInterval ab.1
  let r := if 0 ≤ ab.2 then lu.2 else lu.1
  ab.2 * (r / (1 - r ^ j))

/-- Each actual signed dyadic node is bounded by its rational allowance.
Apply ratio monotonicity with the correct endpoint for the coefficient sign.
This validates both even-conductor and odd-conductor Euler certificates. -/
theorem gamma_dyadic_node_le (j : ℕ) (hj : 0 < j) (ab : ℚ × ℚ)
    (hab : ab ∈ gammaResolventCoefficients) :
    (ab.2 : ℝ) *
        ((2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - ((2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ j)) ≤
      (gammaDyadicNodeUpper j ab : ℝ) := by
  obtain ⟨hl, _, hu, _⟩ := List.forall_iff_forall_mem.mp gamma_dyadic_ratio_checks ab hab
  obtain ⟨hlo, hhi⟩ := gamma_dyadic_ratio_interval_valid ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_lt (K := ℝ)).mpr hu
  norm_num only [Rat.cast_zero, Rat.cast_one] at hlR huR
  have hr0 := hlR.trans hlo
  have hr1 := hhi.trans_lt huR
  by_cases hb : 0 ≤ ab.2
  · simp only [gammaDyadicNodeUpper, ite_eq_left hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonneg_left (Analysis.gamma_geometric_ratio_monotone hr0 hhi huR hj)
        (by exact_mod_cast hb)
  · simp only [gammaDyadicNodeUpper, ite_eq_right hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonpos_left (Analysis.gamma_geometric_ratio_monotone hlR hlo hr1 hj)
        (by exact_mod_cast (le_of_not_ge hb))

end PseudoPrime.AnalyticNumberTheory.Gamma
