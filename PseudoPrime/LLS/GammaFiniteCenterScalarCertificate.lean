/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFiniteCenterArithmeticBounds
public import PseudoPrime.Analysis.GammaFiniteEulerIntervals

/-! # Certified signed scalar inputs for the Euler mass center at cutoff 50000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Rational lower endpoint for arbitrary rational coefficients on
the fixed Gamma node powers. Choose each endpoint by the coefficient sign.
The real interval theorem requires a successful ratio certificate. -/
def gammaFiniteWeightedLower (w : ℚ × ℚ → ℚ) (r : ℚ → ℚ × ℚ) : ℚ :=
  (Analysis.gammaResolventCoefficients.map
      (fun ab ↦ w ab * (if 0 ≤ w ab then (r ab.1).1 else (r ab.1).2))).sum

/-- Rational upper endpoint for arbitrary rational coefficients on
the fixed Gamma node powers. Preserve signed cancellation by choosing
upper power endpoints only for nonnegative coefficients. -/
def gammaFiniteWeightedUpper (w : ℚ × ℚ → ℚ) (r : ℚ → ℚ × ℚ) : ℚ :=
  (Analysis.gammaResolventCoefficients.map
      (fun ab ↦ w ab * (if 0 ≤ w ab then (r ab.1).2 else (r ab.1).1))).sum

/-- A successful ratio check encloses the real weighted fixed-node
sum between its signed rational endpoints for every rational coefficient
function. Sum the node interval bounds and commute rational casts. -/
theorem gamma_finite_weighted_bounds {m : ℚ} {r : ℚ → ℚ × ℚ}
    (hc : Analysis.gammaFiniteEulerRatioCheck m r = true) (w : ℚ × ℚ → ℚ) :
    (gammaFiniteWeightedLower w r : ℝ) ≤
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦ (w ab : ℝ) * (m : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum ∧
      (Analysis.gammaResolventCoefficients.map
            (fun ab ↦ (w ab : ℝ) * (m : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum ≤
        (gammaFiniteWeightedUpper w r : ℝ) := by
  have hl :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦
        (Analysis.signed_rational_node_bounds (b := w ab)
            (Analysis.gamma_finite_ratio_check_sound hc ab hab).1
            (Analysis.gamma_finite_ratio_check_sound hc ab hab).2).1)
  have hu :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦
        (Analysis.signed_rational_node_bounds (b := w ab)
            (Analysis.gamma_finite_ratio_check_sound hc ab hab).1
            (Analysis.gamma_finite_ratio_check_sound hc ab hab).2).2)
  norm_num only [gammaFiniteWeightedLower, gammaFiniteWeightedUpper, Rat.cast_list_sum,
    List.map_map, Function.comp_def]
  exact ⟨hl, hu⟩

/-- The rational coefficient minus b times sigma for a Gamma node.
It expresses the actual logarithmic slope using the common node powers. -/
def gammaSlopeRationalCoefficient (ab : ℚ × ℚ) : ℚ :=
  -ab.2 * (1 / 2 + ab.1)

/-- The rational coefficient a times b times sigma squared over
sigma minus one. At a positive rational cutoff it expresses the actual
integrated linear main term using the common node powers. -/
def gammaTailRationalCoefficient (a : ℚ) (ab : ℚ × ℚ) : ℚ :=
  a * ab.2 * ((1 / 2 + ab.1) ^ 2 / ((1 / 2 + ab.1) - 1))

/-- The actual logarithmic Euler slope equals the fixed-node power
sum with rational slope coefficients. Move negation through the finite
sum and normalize rational casts. Use this identity in scalar certificates. -/
theorem gamma_slope_eq_weighted (m : ℝ) :
    gammaEulerLogSlope m =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ (gammaSlopeRationalCoefficient ab : ℝ) * m ^ (-(1 / 2 + (ab.1 : ℝ))))).sum := by
  rw [gammaEulerLogSlope, List.sum_neg, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ab _
  dsimp only [Function.comp_def, gammaSlopeRationalCoefficient]
  norm_num only [Rat.cast_mul, Rat.cast_neg, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  ring

/-- At a positive rational cutoff, the actual integrated Euler main
equals the power sum with rational tail coefficients. Factor one cutoff
power using the real-power addition identity and normalize the node products. -/
theorem gamma_tail_main_eq_weighted {a : ℚ} (ha : 0 < a) :
    gammaEulerTailMain a =
      (Analysis.gammaResolventCoefficients.map
          (fun ab ↦
            (gammaTailRationalCoefficient a ab : ℝ) * (a : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum := by
  dsimp only [gammaEulerTailMain, gammaRealPowerList]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro ab _
  dsimp only [Function.comp_def, gammaTailRationalCoefficient]
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one]
  rw [show (1 : ℝ) - (1 / 2 + (ab.1 : ℝ)) = -(1 / 2 + (ab.1 : ℝ)) + 1 by ring,
    Real.rpow_add_one ((Rat.cast_pos (K := ℝ)).mpr ha).ne']
  ring

/-- Rational intervals for the fixed node powers at cutoff 50000.
Integer twentieth-power comparisons validate endpoints with denominator
at most one trillion. The certificate below checks all nodes in the kernel. -/
def gammaCenterCutoffRatios (a : ℚ) : ℚ × ℚ :=
  if a = 11 / 20 then (2910861 / 250000000000, 2328689 / 200000000000)
  else
    if a = 13 / 20 then (3946249 / 1000000000000, 3157 / 800000000)
    else
      if a = 4 / 5 then (194661 / 250000000000, 155729 / 200000000000)
      else
        if a = 1 then (44721 / 500000000000, 89443 / 1000000000000)
        else
          if a = 13 / 10 then (1741 / 500000000000, 3483 / 1000000000000)
          else
            if a = 17 / 10 then (9 / 200000000000, 23 / 500000000000)
            else
              if a = 23 / 10 then (0, 1 / 1000000000000)
              else
                if a = 16 / 5 then (0, 1 / 1000000000000)
                else
                  if a = 9 / 2 then (0, 1 / 1000000000000)
                  else if a = 7 then (0, 1 / 1000000000000) else (0, 0)

/-- The cutoff-50000 rational power intervals pass the common
finite ratio checker. Kernel arithmetic proves positivity, exponent
identities and both twentieth-power inequalities for all fixed nodes. -/
theorem gamma_center_cutoff_ratio_check :
    Analysis.gammaFiniteEulerRatioCheck 50000 gammaCenterCutoffRatios = true := by decide +kernel

/-- The rational weight lower bound and signed slope and main
upper bounds satisfy the displayed scalar allowances. Kernel finite
arithmetic retains coefficient signs and certifies all three comparisons. -/
theorem gamma_center_cutoff_rational_checks :
    (6716 / 1000000000 : ℚ) ≤ Analysis.gammaFiniteEulerLower gammaCenterCutoffRatios ∧
      gammaFiniteWeightedUpper gammaSlopeRationalCoefficient gammaCenterCutoffRatios ≤
        (-7106 / 1000000000 : ℚ) ∧
      gammaFiniteWeightedUpper (gammaTailRationalCoefficient 50000) gammaCenterCutoffRatios ≤
        (7257 / 1000 : ℚ) := by
  decide +kernel

/-- The actual Euler weight at 50000 is at least 6716 over one
billion. Connect the real ratio-check bounds to the rational scalar check. -/
theorem gamma_center_cutoff_weight_lower :
    (6716 / 1000000000 : ℝ) ≤ Analysis.gammaResolventEulerWeight 50000 := by
  have hb := (Analysis.gamma_finite_ratio_check_euler_bounds gamma_center_cutoff_ratio_check).1
  have hc := (Rat.cast_le (K := ℝ)).mpr gamma_center_cutoff_rational_checks.1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb hc
  linarith only [hc, hb]

/-- The actual logarithmic Euler slope at 50000 is at most minus
7106 over one billion. Use the signed weighted interval and the exact
slope identity, then apply the kernel rational upper comparison. -/
theorem gamma_center_cutoff_slope_upper : gammaEulerLogSlope 50000 ≤ (-7106 / 1000000000 : ℝ) := by
  have hb :=
    (gamma_finite_weighted_bounds gamma_center_cutoff_ratio_check gammaSlopeRationalCoefficient).2
  have hc := (Rat.cast_le (K := ℝ)).mpr gamma_center_cutoff_rational_checks.2.1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg] at hb hc
  rw [← gamma_slope_eq_weighted] at hb
  linarith only [hb, hc]

/-- The actual integrated Euler main at 50000 is at most 7257/1000.
Use the signed weighted interval and the exact positive-cutoff main
identity, then apply the kernel rational upper comparison. -/
theorem gamma_center_cutoff_main_upper : gammaEulerTailMain 50000 ≤ (7257 / 1000 : ℝ) := by
  have hb :=
    (gamma_finite_weighted_bounds gamma_center_cutoff_ratio_check
        (gammaTailRationalCoefficient 50000)).2
  have hc := (Rat.cast_le (K := ℝ)).mpr gamma_center_cutoff_rational_checks.2.2
  rw [← gamma_tail_main_eq_weighted (by norm_num only : (0 : ℚ) < 50000)] at hb
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb hc
  exact hb.trans hc

/-- Under RH, a finite actual prefix upper bound of 59/10 at cutoff
50000 implies total Euler mass at most 25/2. All boundary, main and error
inputs are proved here or in the arithmetic/error modules; only the
finite prefix upper certificate remains as an explicit input. -/
theorem gamma_mass_le_twelve_half_of_prefix_upper (hRH : RiemannHypothesis)
    (hU :
      (∑ m ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m) ≤
        (59 / 10 : ℝ)) :
    (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) ≤ (25 / 2 : ℝ) := by
  exact
    gamma_mass_le_twelve_half_of_cutoff_inputs hRH hU gamma_center_cutoff_weight_lower
      gamma_center_cutoff_slope_upper gamma_center_cutoff_main_upper

end PseudoPrime.LLS
