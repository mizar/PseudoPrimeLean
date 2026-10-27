/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedCharacterLocalCosts
public import PseudoPrime.Analysis.PhaseResolventCandidate64
public import PseudoPrime.Analysis.GammaDyadicEulerCertificate

/-! # Signed dyadic Euler certificates for the first phase candidate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a rational node. Output: a dyadic Euler-ratio interval with denominator 100000000.
Role: certify the ten new phase-candidate nodes by exact twentieth-power comparisons. -/
def phase64DyadicRatioInterval (a : ℚ) : ℚ × ℚ :=
  if a = 1 then (35355339 / 100000000, 35355340 / 100000000)
  else
    if a = 6 / 5 then (30778610 / 100000000, 30778611 / 100000000)
    else
      if a = 7 / 5 then (26794336 / 100000000, 26794337 / 100000000)
      else
        if a = 5 / 2 then (12500000 / 100000000, 12500001 / 100000000)
        else
          if a = 3 then (8838834 / 100000000, 8838835 / 100000000)
          else
            if a = 5 then (2209708 / 100000000, 2209709 / 100000000)
            else
              if a = 7 then (552427 / 100000000, 552428 / 100000000)
              else
                if a = 10 then (69053 / 100000000, 69054 / 100000000)
                else
                  if a = 15 then (2157 / 100000000, 2158 / 100000000)
                  else if a = 20 then (67 / 100000000, 68 / 100000000) else (0, 0)

/-- Claim: every phase-candidate ratio interval satisfies the exact endpoint power inequalities.
Proof: kernel-check the finite rational computation.
Role: validate the small numerical data without floating-point assumptions. -/
theorem phase64_dyadic_ratio_checks :
    phaseResolvent64Coefficients.Forall
      (fun ab ↦
        let lu := phase64DyadicRatioInterval ab.1
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
theorem phase64_dyadic_ratio_interval_valid (ab : ℚ × ℚ) (hab : ab ∈ phaseResolvent64Coefficients) :
    (phase64DyadicRatioInterval ab.1).1 ≤ (2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      (2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ (phase64DyadicRatioInterval ab.1).2 := by
  obtain ⟨hl, hlu, _, he, hlo, hhi⟩ :=
    List.forall_iff_forall_mem.mp phase64_dyadic_ratio_checks ab hab
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

/-- Input: a progression step and a signed rational node. Output: its rational geometric
upper bound, choosing the interval endpoint according to the coefficient sign.
Role: retain signed cancellation in the exact dyadic cost certificate. -/
def phase64DyadicNodeUpper (j : ℕ) (ab : ℚ × ℚ) : ℚ :=
  let lu := phase64DyadicRatioInterval ab.1
  let r := if 0 ≤ ab.2 then lu.2 else lu.1
  ab.2 * (r / (1 - r ^ j))

/-- Each actual signed dyadic node is bounded by its rational allowance.
Apply ratio monotonicity with the correct endpoint for the coefficient sign.
This validates both even-conductor and odd-conductor Euler certificates. -/
theorem phase64_dyadic_node_le (j : ℕ) (hj : 0 < j) (ab : ℚ × ℚ)
    (hab : ab ∈ phaseResolvent64Coefficients) :
    (ab.2 : ℝ) *
        ((2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - ((2 : ℝ) ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ j)) ≤
      (phase64DyadicNodeUpper j ab : ℝ) := by
  obtain ⟨hl, _, hu, _⟩ := List.forall_iff_forall_mem.mp phase64_dyadic_ratio_checks ab hab
  obtain ⟨hlo, hhi⟩ := phase64_dyadic_ratio_interval_valid ab hab
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl
  have huR := (Rat.cast_lt (K := ℝ)).mpr hu
  norm_num only [Rat.cast_zero, Rat.cast_one] at hlR huR
  have hr0 := hlR.trans hlo
  have hr1 := hhi.trans_lt huR
  by_cases hb : 0 ≤ ab.2
  · simp only [phase64DyadicNodeUpper, ite_eq_left hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonneg_left (gamma_geometric_ratio_monotone hr0 hhi huR hj)
        (by exact_mod_cast hb)
  · simp only [phase64DyadicNodeUpper, ite_eq_right hb, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonpos_left (gamma_geometric_ratio_monotone hlR hlo hr1 hj)
        (by exact_mod_cast (le_of_not_ge hb))

/-- Claim: signed node allowances bound the positive and twice-odd dyadic Euler costs.
Proof: kernel-check the two rational finite sums.
Role: certify numerical margins after retaining coefficient signs. -/
theorem phase64_dyadic_euler_upper_checks :
    (phaseResolvent64Coefficients.map (phase64DyadicNodeUpper 1)).sum ≤ (4532 / 5000 : ℚ) ∧
      2 * (phaseResolvent64Coefficients.map (phase64DyadicNodeUpper 2)).sum ≤
        (1583 / 1250 : ℚ) := by
  decide +kernel

/-- Claim: the exact positive-power cost is at most 0.9064 and twice the odd cost at most 1.2664.
Proof: sum the signed node interval bounds and cast the rational checks.
Role: supply actual Euler-series bounds for the new phase kernel. -/
theorem phase64_dyadic_euler_cost_bounds :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients 2 1 1 ≤ (4532 / 5000 : ℝ) ∧
      2 * finiteSignedPrimeProgressionCost phaseResolvent64Coefficients 2 2 1 ≤
        (1583 / 1250 : ℝ) := by
  have h1 := List.sum_le_sum (fun ab hab ↦ phase64_dyadic_node_le 1 (by norm_num only) ab hab)
  have h2 := List.sum_le_sum (fun ab hab ↦ phase64_dyadic_node_le 2 (by norm_num only) ab hab)
  have hc1 := (Rat.cast_le (K := ℝ)).mpr phase64_dyadic_euler_upper_checks.1
  have hc2 := (Rat.cast_le (K := ℝ)).mpr phase64_dyadic_euler_upper_checks.2
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_div, Rat.cast_list_sum, List.map_map,
    Function.comp_def] at hc1 hc2
  have h1' :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients 2 1 1 ≤
      (phaseResolvent64Coefficients.map (fun ab ↦ (phase64DyadicNodeUpper 1 ab : ℝ))).sum := by
    simpa only [finiteSignedPrimeProgressionCost, pow_one] using h1
  have h2' :
    finiteSignedPrimeProgressionCost phaseResolvent64Coefficients 2 2 1 ≤
      (phaseResolvent64Coefficients.map (fun ab ↦ (phase64DyadicNodeUpper 2 ab : ℝ))).sum := by
    simpa only [finiteSignedPrimeProgressionCost, pow_one] using h2
  constructor
  · linarith only [h1', hc1]
  · linarith only [h2', hc2]

/-- Claim: half the real coefficient sum equals 90992831/200000000.
Proof: evaluate the ten rational coefficients exactly.
Role: match the conductor-log allowance in the actual spectral budget. -/
theorem phase64_coefficient_mass :
    (phaseResolvent64Coefficients.map (fun ab ↦ (ab.2 : ℝ))).sum / 2 =
      (90992831 / 200000000 : ℝ) := by
  norm_num only [phaseResolvent64Coefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]

/-- Claim: every phase-candidate Euler exponent is positive.
Proof: use admissibility from the exact node certificate.
Role: discharge convergence hypotheses of the generic local progression theorems. -/
theorem phase64_node_exponents_pos :
    ∀ ab ∈ phaseResolvent64Coefficients, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
  intro ab hab
  have ha := (finiteSignedPhaseNodeCheck_sound _ phaseResolvent64_node_check).1 ab hab
  have har := (Rat.cast_lt (K := ℝ)).mpr ha
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at har
  linarith only [har]

/-- Claim: the weighted positive cost is at most 0.629 and the weighted minus-one cost,
after the conductor-log-four allowance, at most 0.248.
Proof: combine the signed Euler bounds with the logarithm of two.
Role: keep the true conductor saving in the dyadic budget. -/
theorem phase64_dyadic_weighted_euler_bounds :
    Real.log 2 * finiteSignedPrimeProgressionCost phaseResolvent64Coefficients 2 1 1 ≤
        (629 / 1000 : ℝ) ∧
      2 * (Real.log 2 * finiteSignedPrimeProgressionCost phaseResolvent64Coefficients 2 2 1) -
          (90992831 / 200000000 : ℝ) * Real.log 4 ≤
        (31 / 125 : ℝ) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have h1 := mul_le_mul_of_nonneg_left phase64_dyadic_euler_cost_bounds.1 hl
  have h2 := mul_le_mul_of_nonneg_left phase64_dyadic_euler_cost_bounds.2 hl
  constructor
  · nlinarith only [h1, Real.log_two_lt_d9]
  · rw [Real.log_four_eq]
    nlinarith only [h2, Real.log_two_lt_d9]

/-- Input: any finite positive-power prefix and character value zero at two.
Claim: the actual phase-candidate Euler correction is at most 0.629.
Proof: enlarge the nonnegative combined weight to its exact signed geometric cost.
Role: supply the ramified dyadic branch without a large-scale hypothesis. -/
theorem phase64_dyadic_zero_prefix_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ 2 = 0)
    (K : Finset ℕ) :
    (∑ k ∈ K,
        (1 - (χ ((2 : ℕ) ^ (k + 1))).re) *
          finiteSignedMangoldtWeight phaseResolvent64Coefficients (2 ^ (k + 1))) ≤
      (629 / 1000 : ℝ) := by
  have h :=
    sum_finiteSignedMangoldtWeight_progression_le_cost phaseResolvent64Coefficients
      phase64_node_exponents_pos (fun u hu ↦ phaseResolvent64_euler_nonneg hu) Nat.prime_two
      (by norm_num only : 0 < (1 : ℕ)) (by norm_num only : 0 < (1 : ℕ)) K
  simp only [Nat.one_mul] at h
  simp only [map_pow, Nat.cast_ofNat, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero,
    one_mul]
  exact h.trans phase64_dyadic_weighted_euler_bounds.1

/-- Input: any finite positive-power prefix and character value minus one at two.
Claim: the actual correction minus the conductor-log-four allowance is at most 0.248.
Proof: retain even-power cancellation before using the signed dyadic cost.
Role: supply the minus-one dyadic branch without a large-scale hypothesis. -/
theorem phase64_dyadic_minus_one_prefix_le {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ 2 = -1)
    (K : Finset ℕ) :
    (∑ k ∈ K,
          (1 - (χ ((2 : ℕ) ^ (k + 1))).re) *
            finiteSignedMangoldtWeight phaseResolvent64Coefficients (2 ^ (k + 1))) -
        (90992831 / 200000000 : ℝ) * Real.log 4 ≤
      (31 / 125 : ℝ) := by
  have h :=
    finiteSigned_minus_one_positive_prefix_le_cost χ Nat.prime_two hχ phaseResolvent64Coefficients
      phase64_node_exponents_pos (fun u hu ↦ phaseResolvent64_euler_nonneg hu) K
  have he := phase64_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, he]

end PseudoPrime.Analysis
