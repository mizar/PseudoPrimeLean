/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSquareConductorGap
public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # Positive-coefficient bounds for large-prime Gamma costs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At an input at least one and an exponent at least one, a signed Euler
term is bounded by its positive coefficient times the reciprocal input.
Negative coefficients contribute nonpositively. This keeps their omission
explicit when constructing the large-prime upper envelope. -/
theorem gamma_signed_power_le_positive_reciprocal {u a b : ℝ} (hu : 1 ≤ u) (ha : 1 ≤ a) :
    b * u ^ (-a) ≤ max b 0 * u⁻¹ := by
  have hr : u ^ (-a) ≤ u⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hu (neg_le_neg ha)
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    exact mul_le_mul_of_nonneg_left hr hb
  · rw [max_eq_right (le_of_not_ge hb), zero_mul]
    exact
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hb) (Real.rpow_nonneg (zero_le_one.trans hu) _)

/-- The total positive coefficient of the signed resolvent is exactly
79977719/25000000. Direct rational arithmetic certifies the coefficient used
in large-prime envelopes without taking absolute values of negative terms. -/
theorem gamma_positive_coefficient_mass :
    (gammaResolventCoefficients.map (fun ab ↦ max (ab.2 : ℝ) 0)).sum =
      (79977719 / 25000000 : ℝ) := by
  norm_num only [gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, max_eq_left, max_eq_right]

/-- A finite signed family with exponents at least one is bounded by its
positive coefficient mass times the reciprocal input. Apply the pointwise
signed bound and add the inequalities. This is the finite-list envelope
underlying both ordinary and odd prime-power costs. -/
theorem gamma_signed_list_le_positive_reciprocal (l : List (ℚ × ℚ)) {u : ℝ} (hu : 1 ≤ u)
    (ha : ∀ ab ∈ l, (1 : ℝ) ≤ 1 / 2 + (ab.1 : ℝ)) :
    (l.map (fun ab ↦ (ab.2 : ℝ) * u ^ (-(1 / 2 + (ab.1 : ℝ))))).sum ≤
      (l.map (fun ab ↦ max (ab.2 : ℝ) 0)).sum * u⁻¹ := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, zero_mul, le_refl]
  | cons ab l
    ih =>
    have hhead :=
      gamma_signed_power_le_positive_reciprocal hu (ha ab (List.mem_cons_self)) (b := (ab.2 : ℝ))
    have htail := ih (fun cd hcd ↦ ha cd (List.mem_cons_of_mem ab hcd))
    simpa only [List.map_cons, List.sum_cons, add_mul] using add_le_add hhead htail

/-- At every real input at least one, the actual signed Gamma Euler weight
is bounded by the certified positive coefficient mass divided by the input.
Apply the finite-list inequality using the verified resolvent scales.
This supplies the reciprocal envelope for large-prime power sums. -/
theorem gamma_euler_weight_le_positive_reciprocal {u : ℝ} (hu : 1 ≤ u) :
    gammaResolventEulerWeight u ≤ (79977719 / 25000000 : ℝ) * u⁻¹ := by
  have ha : ∀ ab ∈ gammaResolventCoefficients, (1 : ℝ) ≤ 1 / 2 + (ab.1 : ℝ) := by
    intro ab hab
    have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) :=
      Rat.cast_lt.mpr (List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab)
    norm_num only at h
    linarith only [h]
  simpa only [gammaResolventEulerWeight, gamma_positive_coefficient_mass] using
    gamma_signed_list_le_positive_reciprocal gammaResolventCoefficients hu ha

/-- For a base greater than one, the exact signed odd-power Euler cost
is at most the positive coefficient mass times the reciprocal geometric sum.
Compare the two summable series termwise using the actual Euler envelope.
This is the large-prime bound before algebraic normalization. -/
theorem gamma_odd_euler_cost_le_positive_geometric {p : ℝ} (hp : 1 < p) :
    gammaPrimeOddEulerCost p ≤
      (79977719 / 25000000 : ℝ) * (p ^ (-1 : ℝ) / (1 - (p ^ (-1 : ℝ)) ^ 2)) := by
  have hσ : (0 : ℝ) < 1 := zero_lt_one
  have hs := (summable_gamma_euler_odd_powers hp hσ).mul_left (79977719 / 25000000 : ℝ)
  have hle :=
    (summable_gammaResolventEulerWeight_odd_powers hp).tsum_le_tsum
      (fun k ↦ by
        simpa only [Real.rpow_neg_one] using
          gamma_euler_weight_le_positive_reciprocal (one_le_pow₀ hp.le : (1 : ℝ) ≤ p ^ (2 * k + 1)))
      hs
  rw [tsum_gammaResolventEulerWeight_odd_powers_eq_cost hp, tsum_mul_left,
    tsum_gamma_euler_odd_powers hp hσ] at hle
  exact hle

/-- The reciprocal odd-power geometric ratio equals the reciprocal of
p minus its reciprocal for p greater than one. Factor the denominator
and cancel the nonzero reciprocal. This converts the series bound to
the form used for large-prime numerical certificates. -/
theorem gamma_reciprocal_odd_geometric_eq {p : ℝ} (hp : 1 < p) :
    p ^ (-1 : ℝ) / (1 - (p ^ (-1 : ℝ)) ^ 2) = 1 / (p - p⁻¹) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have he : 1 - (p⁻¹) ^ 2 = p⁻¹ * (p - p⁻¹) := by rw [mul_sub, inv_mul_cancel₀ hp0, pow_two]
  rw [Real.rpow_neg_one, he, mul_comm p⁻¹ (p - p⁻¹)]
  simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - p⁻¹) (inv_ne_zero hp0)

/-- For every scale at least 10000, the cutoff logarithm plus one divided
by the square root is at most 23/100. Bound log x through the square root
of sqrt x and use the threshold for both square roots. This is a uniform
scale certificate, not an evaluation at one endpoint. -/
theorem gamma_large_scale_ramp_bound {x : ℝ} (hx : 10000 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) + 1) / Real.sqrt x ≤ (23 / 100 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht : (100 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) hx0.le).mpr
      (by
        norm_num only; exact hx)
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs : (10 : ℝ) ≤ Real.sqrt (Real.sqrt x) :=
    (Real.le_sqrt (by norm_num only) ht0.le).mpr
      (by
        norm_num only; exact ht)
  have hsq := Real.sq_sqrt ht0.le
  have hb : 2 * Real.sqrt (Real.sqrt x) ≤ Real.sqrt x / 5 := by nlinarith only [hs, hsq]
  have hl := log_le_sqrt_of_pos ht0
  have he := Real.log_sqrt hx0.le
  have hc : Real.log (99 / 40 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 99 / 40)
    linarith only [h]
  rw [Real.log_mul (by norm_num only : (99 / 40 : ℝ) ≠ 0) hx0.ne']
  apply (div_le_iff₀ ht0).mpr
  nlinarith only [hl, he, hc, hb, ht]

/-- For every real base at least eleven, twice the exact signed odd Euler
cost is at most 3/5. Bound the reciprocal by 1/11 and use the positive
coefficient envelope. This uniform prime bound leaves a fixed allowance
for the ramp correction in the conductor-gap absorption. -/
theorem gamma_large_prime_odd_cost_le {p : ℝ} (hp : 11 ≤ p) :
    2 * gammaPrimeOddEulerCost p ≤ (3 / 5 : ℝ) := by
  have hp1 : 1 < p := by linarith only [hp]
  have hi : p⁻¹ ≤ (11 : ℝ)⁻¹ := (inv_le_inv₀ (zero_lt_one.trans hp1) (by norm_num only)).mpr hp
  have hd : 0 < p - p⁻¹ := by
    norm_num only at hi; linarith only [hp, hi]
  have h := gamma_odd_euler_cost_le_positive_geometric hp1
  rw [gamma_reciprocal_odd_geometric_eq hp1] at h
  have hu : (79977719 / 25000000 : ℝ) * (1 / (p - p⁻¹)) ≤ 3 / 10 := by
    rw [mul_one_div, div_le_iff₀ hd]
    norm_num only at hi
    linarith only [hp, hi]
  linarith only [h, hu]

/-- For every natural base at least eleven and every scale at least 10000,
the actual square-prime combined allowance is at most 83/100, hence below
twice the certified conductor coefficient. Use the exact signed Euler
bound and the uniform logarithmic ramp bound. No per-prime cost assumption
is needed on this large-prime range. -/
theorem gamma_large_prime_square_cost_le {p : ℕ} (hp : 11 ≤ p) {x : ℝ} (hx : 10000 ≤ x) :
    gammaSquareCombinedCost p x ≤ (83 / 100 : ℝ) := by
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num only : (1 : ℕ) < 11) hp
  have hx1 : 1 ≤ x := by linarith only [hx]
  have he := gamma_large_prime_odd_cost_le hpR
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [pow_two, Nat.cast_ofNat] at h
    exact h
  have hlp : (1 : ℝ) ≤ Real.log p := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 4) (by linarith only [hpR] : (4 : ℝ) ≤ p)
    linarith only [h, hl4, Real.log_two_gt_d9]
  have hcut : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg (by nlinarith only [hx1])
  have hdiv : Real.log ((99 / 40 : ℝ) * x) / Real.log p ≤ Real.log ((99 / 40 : ℝ) * x) := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hlp)).mpr
    nlinarith only [hcut, hlp]
  have hr :=
    (div_le_div_of_nonneg_right (add_le_add hdiv le_rfl) (Real.sqrt_nonneg x)).trans
      (gamma_large_scale_ramp_bound hx)
  have h := gamma_square_combined_cost_le_log hp1 hx1
  linarith only [he, hr, h]

/-- At scales at least 10000, the actual losses from selected primes at least
eleven are absorbed by the conductor gap with the certified coefficient.
Apply the uniform combined-cost certificate to remove the abstract numerical
local-cost hypothesis on the large-prime range. -/
theorem gamma_large_prime_actual_cost_absorbed_by_conductor_gap {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 10000 ≤ x) (hlarge : ∀ p ∈ S, 11 ≤ p) :
    (11783423 / 25000000 : ℝ) * Real.log f +
        (∑ p ∈ S,
          ((∑ k ∈ K p,
              (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) +
            Real.log p *
              ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
                Real.sqrt x))) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  apply
    gamma_minus_one_actual_cost_absorbed_by_conductor_gap hn hd hm hf hdf hfd S hS χ hχ K
      (by linarith only [hx]) (by norm_num only)
  intro p hp
  exact
    (gamma_large_prime_square_cost_le (hlarge p hp) hx).trans
      (by norm_num only : (83 / 100 : ℝ) ≤ 2 * (11783423 / 25000000 : ℝ))

end PseudoPrime.Analysis
