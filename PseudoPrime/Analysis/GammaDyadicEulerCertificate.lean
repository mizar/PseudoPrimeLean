/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicIntervalBounds

/-! # Rational certificates for signed dyadic Euler costs -/

@[expose] public section

namespace PseudoPrime.Analysis

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
          20 * ab.1 + 10 = (gammaSmallPrimeRatioExponent ab.1 : ℚ) ∧
          lu.1 ^ 20 * 2 ^ gammaSmallPrimeRatioExponent ab.1 ≤ 1 ∧
          1 ≤ lu.2 ^ 20 * 2 ^ gammaSmallPrimeRatioExponent ab.1) := by
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
  have hexp : -(gammaSmallPrimeRatioExponent ab.1 : ℝ) / 20 = -(1 / 2 + (ab.1 : ℝ)) := by
    linarith only [heR]
  simpa only [hexp] using
    gamma_rpow_neg_twentieth_interval (by norm_num only : (0 : ℝ) < 2) hlR (hlR.trans huR)
      (gammaSmallPrimeRatioExponent ab.1) hloR hhiR

/-- For any positive natural exponent, r/(1-r^j) increases on [0,1).
Power monotonicity makes its positive denominator decrease. This common
comparison handles both positive-power and odd-power dyadic costs. -/
theorem gamma_geometric_ratio_monotone {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) {j : ℕ}
    (hj : 0 < j) : r / (1 - r ^ j) ≤ s / (1 - s ^ j) := by
  have hs0 : 0 ≤ s := hr.trans hrs
  have hd : 0 < 1 - s ^ j := sub_pos.mpr (pow_lt_one₀ hs0 hs hj.ne')
  have hds : 1 - s ^ j ≤ 1 - r ^ j := sub_le_sub_left (pow_le_pow_left₀ hr hrs j) 1
  exact div_le_div₀ hs0 hrs hd hds

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
      mul_le_mul_of_nonneg_left (gamma_geometric_ratio_monotone hr0 hhi huR hj)
        (by exact_mod_cast hb)
  · simp only [gammaDyadicNodeUpper, ite_eq_right hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonpos_left (gamma_geometric_ratio_monotone hlR hlo hr1 hj)
        (by exact_mod_cast (le_of_not_ge hb))

/-- Rational arithmetic bounds the full dyadic Euler cost by 9883/10000
and twice the odd-power cost by 545/400. All signed node contributions
remain in the finite sum. Kernel computation certifies both numerical margins. -/
theorem gamma_dyadic_euler_upper_checks :
    (gammaResolventCoefficients.map (gammaDyadicNodeUpper 1)).sum ≤ (9883 / 10000 : ℚ) ∧
      2 * (gammaResolventCoefficients.map (gammaDyadicNodeUpper 2)).sum ≤ (545 / 400 : ℚ) := by
  decide +kernel

/-- The actual signed dyadic Euler costs satisfy the finite rational bounds.
Sum the node inequalities and cast the kernel certificates into the reals.
These are unconditional bounds for the dyadic terms in both conductor parities. -/
theorem gamma_dyadic_euler_cost_bounds :
    gammaPrimeEulerCost 2 ≤ (9883 / 10000 : ℝ) ∧
      2 * gammaPrimeOddEulerCost 2 ≤ (545 / 400 : ℝ) := by
  have h1 := List.sum_le_sum (fun ab hab ↦ gamma_dyadic_node_le 1 (by norm_num only) ab hab)
  have h2 := List.sum_le_sum (fun ab hab ↦ gamma_dyadic_node_le 2 (by norm_num only) ab hab)
  simp only [pow_one] at h1
  change gammaPrimeEulerCost 2 ≤ _ at h1
  change gammaPrimeOddEulerCost 2 ≤ _ at h2
  have hc1 := (Rat.cast_le (K := ℝ)).mpr gamma_dyadic_euler_upper_checks.1
  have hc2 := (Rat.cast_le (K := ℝ)).mpr gamma_dyadic_euler_upper_checks.2
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc1 hc2
  constructor
  · linarith only [h1, hc1]
  · linarith only [h2, hc2]

/-- The weighted full dyadic Euler cost is at most 6851/10000. For the
odd-conductor minus-one branch, subtract the actual conductor difference
M log four, giving a weighted odd Euler cost at most 3/10. Certified log
two bounds and the signed ratio certificate prove both margins. -/
theorem gamma_dyadic_weighted_euler_bounds :
    Real.log 2 * gammaPrimeEulerCost 2 ≤ (6851 / 10000 : ℝ) ∧
      2 * (Real.log 2 * gammaPrimeOddEulerCost 2) - (11783423 / 25000000 : ℝ) * Real.log 4 ≤
        (3 / 10 : ℝ) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have h1 := mul_le_mul_of_nonneg_left gamma_dyadic_euler_cost_bounds.1 hl
  have h2 := mul_le_mul_of_nonneg_left gamma_dyadic_euler_cost_bounds.2 hl
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [Nat.cast_ofNat] at h
    exact h
  constructor
  · nlinarith only [h1, Real.log_two_lt_d9]
  · rw [he]
    nlinarith only [h2, Real.log_two_lt_d9]

/-- For every scale at least 10000, the actual weighted minus-one dyadic
ramp series is at most 9/50. Bound the cutoff count by its logarithmic
quotient and use log two below one. The signed parity and cutoff tail
are retained by the existing actual-series bound. -/
theorem gamma_dyadic_minus_one_actual_ramp_le {x : ℝ} (hx : 10000 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (9 / 50 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hl1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hr :=
    (gamma_ramp_neg_one_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0).trans
      (div_le_div_of_nonneg_right
        (add_le_add (gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ)) hx1) le_rfl)
        (Real.sqrt_nonneg x))
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2 + 1) / Real.sqrt x) =
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_add, mul_one,
      mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2), div_mul_cancel₀ _ hl0.ne']
  norm_num only [Nat.cast_ofNat] at hw
  rw [he] at hw
  exact
    hw.trans
      ((div_le_div_of_nonneg_right (add_le_add le_rfl hl1) (Real.sqrt_nonneg x)).trans
        (gamma_small_prime_scale_ramp_bound hx))

/-- With character value minus one at two, the actual finite odd Euler
loss and full signed ramp loss, after subtracting M log four, total at
most 12/25 for every scale at least 10000. Apply both signed certificates.
This is the dyadic cost budget for the odd-conductor minus-one branch;
the arithmetic availability of the log-four gap is a separate conductor input. -/
theorem gamma_dyadic_minus_one_actual_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = -1)
    (K : Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) :
    (∑ k ∈ K, (1 - (χ (2 ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (2 ^ (2 * k + 1))) +
          Real.log 2 *
            ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
              Real.sqrt x) -
        (11783423 / 25000000 : ℝ) * Real.log 4 ≤
      (12 / 25 : ℝ) := by
  have he := gamma_minus_one_odd_prime_correction_le_cost χ Nat.prime_two hχ K
  have hr := gamma_dyadic_minus_one_actual_ramp_le hx
  have hc := gamma_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at he
  linarith only [he, hr, hc]

end PseudoPrime.Analysis
