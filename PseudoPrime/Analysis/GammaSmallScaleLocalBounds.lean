/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogSqrtTangentBounds
public import PseudoPrime.Analysis.GammaActualRamifiedBudget

/-! # Smaller-scale square-part and dyadic Gamma budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every x ≥ 4096, the cutoff logarithm plus one divided by sqrt(x)
is at most 1/6. Apply the generic tangent bound at a=64.
Certified logarithms of two and exp(1) verify the real anchor.
This is shared by all prime-local small-scale costs. -/
theorem gamma_cutoff_log_ramp_le_sixth {x : ℝ} (hx : 4096 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) + 1) / Real.sqrt x ≤ (1 / 6 : ℝ) := by
  have hc : Real.log (99 / 40 : ℝ) ≤ 1 := by
    apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 99 / 40)).mpr
    exact (by norm_num only : (99 / 40 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  exact
    log_mul_add_div_sqrt_le_of_anchor (a := 64) (by norm_num only) (by norm_num only)
      (by
        norm_num only; exact hx)
      (by
        rw [h64]; linarith only [hc, Real.log_two_lt_d9])
      (by norm_num only)

/-- At any natural base p ≥ 3 and x ≥ 4096, the per-log-prime ramp
allowance is at most 1/6. Bound log(p) below by one and use the
common cutoff estimate. This supplies the odd-prime local comparison. -/
theorem gamma_odd_prime_log_ramp_le_sixth {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 4096 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1) / Real.sqrt x ≤ (1 / 6 : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : (1 : ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hpR
    linarith only [h, Real.log_three_gt_d9]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hcut : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg (by nlinarith only [hx1])
  have hdiv : Real.log ((99 / 40 : ℝ) * x) / Real.log p ≤ Real.log ((99 / 40 : ℝ) * x) := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hlp)).mpr
    nlinarith only [hcut, hlp]
  exact
    (div_le_div_of_nonneg_right (add_le_add hdiv le_rfl) (Real.sqrt_nonneg x)).trans
      (gamma_cutoff_log_ramp_le_sixth hx)

/-- Every odd prime p ≥ 3 at scale x ≥ 4096 has combined square cost
at most 139/150, hence below twice the conductor coefficient.
Use signed Euler certificates for 3,5,7 and the large-prime Euler bound,
then add the common 1/6 ramp allowance. No input enumeration is involved. -/
theorem gamma_odd_prime_square_cost_le_small_scale {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x : ℝ}
    (hx : 4096 ≤ x) : gammaSquareCombinedCost p x ≤ (139 / 150 : ℝ) := by
  have he : 2 * gammaPrimeOddEulerCost p ≤ (19 / 25 : ℝ) := by
    by_cases hlarge : 11 ≤ p
    · exact (gamma_large_prime_odd_cost_le (by exact_mod_cast hlarge)).trans (by norm_num only)
    · have hfinite : ∀ q ∈ Finset.range 11, q.Prime → 3 ≤ q → q ∈ ([3, 5, 7] : List ℕ) := by
        decide +kernel
      exact
        gamma_small_prime_odd_cost_le
          (hfinite p (Finset.mem_range.mpr (lt_of_not_ge hlarge)) hp hp3)
  have hr := gamma_odd_prime_log_ramp_le_sixth hp3 hx
  have hc :=
    gamma_square_combined_cost_le_log (lt_of_lt_of_le (by norm_num only : (1 : ℕ) < 3) hp3)
      (by linarith only [hx] : (1 : ℝ) ≤ x)
  linarith only [he, hr, hc]

/-- For odd input prime factors with value minus one and any positive-power
prefix, x ≥ 4096 suffices to bound their actual total loss by 2M times
their logarithmic weight. Use the improved 139/150 per-prime allowance.
This is the common input for both conductor-gap absorptions. -/
theorem gamma_actual_square_sum_le_small_scale {n f : ℕ} (hn : Odd n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 4096 ≤ x) :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (∑ p ∈ S, Real.log p) * (2 * (11783423 / 25000000 : ℝ)) := by
  have hpoint :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      ∑ p ∈ S, Real.log p * (2 * (11783423 / 25000000 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (hS hp)
    have hpne : p ≠ 2 := fun he ↦ hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hS hp))
    have hp3 : 3 ≤ p := Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm hpne))
    exact
      (gamma_actual_minus_one_prime_cost_le χ hprime (hχ p hp) (K p) (by linarith only [hx])).trans
        (mul_le_mul_of_nonneg_left
          ((gamma_odd_prime_square_cost_le_small_scale hprime hp3 hx).trans (by norm_num only))
          (Real.log_natCast_nonneg p))
  simpa only [Finset.sum_mul] using hpoint

/-- For n=d t² odd and d dividing f≤4d, actual square losses are absorbed
by the ambient conductor gap at every x ≥ 4096. Combine the improved
prime sum with the existing exact logarithmic gap. This removes the
scale-10000 restriction from square-part absorption. -/
theorem gamma_actual_square_absorbed_small_scale {n d t f : ℕ} (hn : n = d * t ^ 2) (hodd : Odd n)
    (hd : 0 < d) (ht : 0 < t) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 4096 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  have hs := gamma_actual_square_sum_le_small_scale hodd S hS χ hχ K hx
  have hg :=
    gamma_square_only_prime_log_gap_budget hn hd ht hf hdf hfd S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hs, hw]

/-- For n=f t² odd, actual square losses use only M(log n-log f) at x ≥ 4096.
The exact odd-conductor logarithmic gap leaves M log four available for two.
This is the sharper conductor branch before the dyadic cost is added. -/
theorem gamma_actual_odd_square_absorbed_small_scale {n t f : ℕ} (hn : n = f * t ^ 2) (hodd : Odd n)
    (hf : 0 < f) (ht : 0 < t) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x : ℝ} (hx : 4096 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log n := by
  have hs := gamma_actual_square_sum_le_small_scale hodd S hS χ hχ K hx
  have hg :=
    gamma_odd_conductor_square_log_budget hn hf ht S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hs, hw]

/-- For the minus-one branch at two and all x ≥ 4096, the actual weighted
ramp series is at most 1/6. Retain the signed-tail series bound and cancel log two
in the cutoff count. This supplies the small-scale odd-conductor dyadic allowance. -/
theorem gamma_dyadic_minus_one_ramp_le_small_scale {x : ℝ} (hx : 4096 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (1 / 6 : ℝ) := by
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
        (gamma_cutoff_log_ramp_le_sixth hx))

/-- At value minus one at two and scale x ≥ 4096, the actual dyadic
cost minus M log four is at most 7/15. Add the certified 3/10 Euler difference
to the improved 1/6 ramp bound. The full positive-power prefix is retained. -/
theorem gamma_actual_dyadic_minus_one_cost_small_scale {f : ℕ} (χ : DirichletCharacter ℂ f)
    (hχ : χ 2 = -1) (K : Finset ℕ) {x : ℝ} (hx : 4096 ≤ x) :
    gammaActualPrimeLocalCost χ 2 K x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤ (7 / 15 : ℝ) := by
  have he := gamma_minus_one_positive_prime_correction_le_cost χ Nat.prime_two hχ K
  have hr := gamma_dyadic_minus_one_ramp_le_small_scale hx
  have hc := gamma_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [gammaActualPrimeLocalCost]
  rw [show χ ((2 : ℕ) : ZMod f) = -1 by simpa only [Nat.cast_ofNat] using hχ]
  norm_num only [Nat.cast_ofNat]
  linarith only [he, hr, hc]

/-- For the zero branch at two and every x ≥ 4096, the weighted ramp
series is at most 1/6. Cancel log two in the cutoff count and apply the
common logarithmic bound. This keeps a uniform small-scale ramified budget. -/
theorem gamma_dyadic_zero_ramp_le_small_scale {x : ℝ} (hx : 4096 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (1 / 6 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hr :=
    (gamma_ramp_zero_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0).trans
      (div_le_div_of_nonneg_right (gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ)) hx1)
        (Real.sqrt_nonneg x))
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  norm_num only [Nat.cast_ofNat] at hw
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2) / Real.sqrt x) =
      Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2),
      div_mul_cancel₀ _ hl0.ne']
  rw [he] at hw
  have hsmall := gamma_cutoff_log_ramp_le_sixth hx
  have hmono :=
    div_le_div_of_nonneg_right
      (show Real.log ((99 / 40 : ℝ) * x) ≤ Real.log ((99 / 40 : ℝ) * x) + 1 by linarith only)
      (Real.sqrt_nonneg x)
  exact hw.trans (hmono.trans hsmall)

/-- At value zero at two and x ≥ 4096, the actual dyadic cost for any
positive-power prefix is at most 13/15. Add the certified full Euler cost
6851/10000 to the ramp bound 1/6. This relaxed allowance applies below the
old scale-20000 gate without asserting its sharper three-quarter constant. -/
theorem gamma_actual_dyadic_zero_cost_small_scale {f : ℕ} (χ : DirichletCharacter ℂ f)
    (hχ : χ 2 = 0) (K : Finset ℕ) {x : ℝ} (hx : 4096 ≤ x) :
    gammaActualPrimeLocalCost χ 2 K x ≤ (13 / 15 : ℝ) := by
  have he := sum_gammaResolventMangoldtWeight_primePowers_le_cost Nat.prime_two K
  have hr := gamma_dyadic_zero_ramp_le_small_scale hx
  have hc := gamma_dyadic_weighted_euler_bounds.1
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [gammaActualPrimeLocalCost]
  simp only [Nat.cast_ofNat, map_pow, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero,
    one_mul]
  linarith only [he, hr, hc]

end PseudoPrime.Analysis
