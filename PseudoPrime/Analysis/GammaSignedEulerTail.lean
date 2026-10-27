/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicAnchorBounds

/-! # Exact signed Euler prefixes and uniformly bounded anchored tails -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real p>1 and any finite length N. Claim: the exact Euler cost equals the signed
prefix through p^N plus the remaining signed tail. Proof: split the absolutely convergent
series. Role: keep finite-scale cancellation before applying any positive tail envelope. -/
theorem gamma_prime_euler_cost_split (p : ℝ) (hp : 1 < p) (N : ℕ) :
    gammaPrimeEulerCost p =
      (∑ k ∈ Finset.range N, gammaResolventEulerWeight (p ^ (k + 1))) +
        ∑' k : ℕ, gammaResolventEulerWeight (p ^ (k + N + 1)) := by
  have h := (summable_gammaResolventEulerWeight_powers hp).sum_add_tsum_nat_add N
  rw [tsum_gammaResolventEulerWeight_powers_eq_cost hp] at h
  exact h.symm

/-- Input: p>1, a real coefficient and any finite length N.
Claim: the reciprocal tail equals C/(p^N*(p-1)). Proof: factor p^N and sum the geometric
series. Role: normalize the cost of a tail envelope after retaining a finite prefix. -/
theorem gamma_reciprocal_power_tail_sum {p C : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑' k : ℕ, C * (p ^ (k + N + 1))⁻¹) = C / (p ^ N * (p - 1)) := by
  have ht (k : ℕ) : C * (p ^ (k + N + 1))⁻¹ = (p ^ N)⁻¹ * (C * (p ^ (k + 1))⁻¹) := by
    rw [Nat.add_right_comm k N 1, pow_add, mul_inv_rev]
    ring
  simp only [ht, tsum_mul_left]
  have hg := tsum_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)
  norm_num only [Real.rpow_neg_one] at hg
  rw [hg]
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hr : p⁻¹ / (1 - p⁻¹) = 1 / (p - 1) := by
    have he : 1 - p⁻¹ = p⁻¹ * (p - 1) := by rw [mul_sub, inv_mul_cancel₀ hp0, mul_one]
    rw [he, mul_comm p⁻¹ (p - 1)]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - 1) (inv_ne_zero hp0)
  rw [hr]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Input: a>0, p>1, a<=p^(N+1), and an anchored coefficient cap C.
Claim: the remaining signed Euler tail is at most C/(p^N*(p-1)).
Proof: every remaining power is above the anchor; compare absolutely convergent sums.
Role: let the tail use a larger anchor than the first prime power. -/
theorem gamma_euler_signed_tail_le_anchored {a p C : ℝ} (ha : 0 < a) (hp : 1 < p) (N : ℕ)
    (hap : a ≤ p ^ (N + 1)) (hC : gammaAnchoredReciprocalCoefficient a ≤ C) :
    (∑' k : ℕ, gammaResolventEulerWeight (p ^ (k + N + 1))) ≤ C / (p ^ N * (p - 1)) := by
  have hw := (summable_nat_add_iff N).mpr (summable_gammaResolventEulerWeight_powers hp)
  have hg0 : Summable (fun k : ℕ ↦ C * (p ^ (k + 1))⁻¹) := by
    simpa only [Real.rpow_neg_one] using
      (summable_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)).mul_left C
  have hg := (summable_nat_add_iff N).mpr hg0
  have he (k : ℕ) : gammaResolventEulerWeight (p ^ (k + N + 1)) ≤ C * (p ^ (k + N + 1))⁻¹ := by
    have hpow : a ≤ p ^ (k + N + 1) := by
      apply hap.trans
      calc
        _ = 1 * p ^ (N + 1) := (one_mul _).symm
        _ ≤ p ^ k * p ^ (N + 1) :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hp.le) (pow_nonneg (zero_lt_one.trans hp).le _)
        _ = p ^ (k + (N + 1)) := (pow_add p k (N + 1)).symm
        _ = p ^ (k + N + 1) := by rw [Nat.add_assoc]
    have h := gamma_euler_weight_le_anchored_reciprocal ha hpow
    exact
      h.trans
        (mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hp).le _)))
  have htail := hw.tsum_le_tsum he hg
  rw [gamma_reciprocal_power_tail_sum hp N] at htail
  exact htail

/-- Input: the same anchor and finite-prefix data. Claim: the actual signed Euler cost is
bounded by its exact finite prefix plus the certified reciprocal tail.
Proof: combine the exact split and tail theorem. Role: sharpen local Euler allowances. -/
theorem gamma_prime_euler_cost_le_signed_prefix_tail {a p C : ℝ} (ha : 0 < a) (hp : 1 < p) (N : ℕ)
    (hap : a ≤ p ^ (N + 1)) (hC : gammaAnchoredReciprocalCoefficient a ≤ C) :
    gammaPrimeEulerCost p ≤
      (∑ k ∈ Finset.range N, gammaResolventEulerWeight (p ^ (k + 1))) + C / (p ^ N * (p - 1)) := by
  rw [gamma_prime_euler_cost_split p hp N]
  exact add_le_add (le_refl _) (gamma_euler_signed_tail_le_anchored ha hp N hap hC)

/-- Input: p>1, a certified dyadic anchor below p^2 and checked node intervals at p.
Claim: the exact signed Euler cost obeys the displayed rational first-term/tail allowance.
Proof: retain the first signed term and bound the remaining tail from the larger anchor.
Role: discharge local Euler hypotheses using the existing finite node-check interface. -/
theorem gamma_prime_euler_cost_le_first_term_certificate {p a : ℕ} (hp : 1 < p)
    (ha : a ∈ gammaDyadicAnchors) (hap : a ≤ p ^ 2) {r : ℚ → ℚ × ℚ}
    (hc : gammaFiniteEulerRatioCheck p r = true) :
    gammaPrimeEulerCost p ≤
      ((gammaFiniteEulerUpper r + gammaDyadicAnchorCap a / ((p : ℚ) * ((p : ℚ) - 1)) : ℚ) : ℝ) := by
  have hpos : (0 : ℚ) < a := (of_decide_eq_true (gamma_dyadic_anchor_checks a ha).1).1
  have haR := Rat.cast_pos (K := ℝ).mpr hpos
  norm_num only [Rat.cast_natCast] at haR
  have htail :=
    gamma_prime_euler_cost_le_signed_prefix_tail haR (show (1 : ℝ) < p by exact_mod_cast hp) 1
      (show (a : ℝ) ≤ (p : ℝ) ^ (1 + 1) by exact_mod_cast hap)
      (gamma_dyadic_anchor_coefficient_le ha)
  have hfirst := (gamma_finite_ratio_check_euler_bounds hc).2
  norm_num only [Finset.sum_range_one, pow_one, Rat.cast_natCast] at htail hfirst
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast,
    Rat.cast_one]
  exact htail.trans (add_le_add hfirst (le_refl _))

end PseudoPrime.Analysis
