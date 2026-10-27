/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSmallScaleLocalBounds

/-! # Scale-dependent local costs for quadratic witness comparisons -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The unrounded logarithmic ramp allowance at scale x. Input x>=1 is
supplied by comparison theorems. Role: replace the fixed one-sixth allowance. -/
noncomputable def gammaVariableRampAllowance (x : ℝ) : ℝ :=
  (Real.log ((99 / 40 : ℝ) * x) + 1) / Real.sqrt x

/-- The conductor coefficient enlarged enough to absorb all odd square losses.
It is the maximum of the kernel mass and half the Euler-plus-ramp allowance.
Role: keep local losses valid when the scale is below 4096. -/
noncomputable def gammaVariableSquareMass (x : ℝ) : ℝ :=
  max (11783423 / 25000000 : ℝ) ((19 / 25 + gammaVariableRampAllowance x) / 2)

/-- The dyadic allowance combines the certified full Euler contribution at two
with the unrounded ramp error. Role: cover zero, minus-one and one branches. -/
noncomputable def gammaVariableDyadicAllowance (x : ℝ) : ℝ :=
  6851 / 10000 + gammaVariableRampAllowance x

/-- Input: x>=1. Claim: the variable ramp allowance is nonnegative.
Use positivity of the cutoff logarithm and square root. Role: support local budgets. -/
theorem gamma_variable_ramp_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ gammaVariableRampAllowance x := by
  have hl := Real.log_nonneg (show (1 : ℝ) ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  exact div_nonneg (by linarith only [hl]) (Real.sqrt_nonneg x)

/-- At every real scale, the variable square coefficient dominates the fixed
kernel mass. Role: enlarge the conductor contribution without losing its sign. -/
theorem gamma_variable_square_mass_ge (x : ℝ) :
    (11783423 / 25000000 : ℝ) ≤ gammaVariableSquareMass x := by exact le_max_left _ _

/-- Input: x>=1. Claim: the variable dyadic allowance is nonnegative.
Add the nonnegative ramp allowance. Role: include the nonpositive one branch. -/
theorem gamma_variable_dyadic_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ gammaVariableDyadicAllowance x := by
  dsimp only [gammaVariableDyadicAllowance]
  linarith only [gamma_variable_ramp_nonneg hx]

/-- Input: p>=3 and x>=1. Claim: the odd-prime normalized ramp cost is
bounded by the unrounded common allowance. Use log(p)>=1.
Role: retain scale dependence instead of a fixed cutoff gate. -/
theorem gamma_odd_prime_log_ramp_le_variable {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) / Real.log p + 1) / Real.sqrt x ≤
      gammaVariableRampAllowance x := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hlp : (1 : ℝ) ≤ Real.log p := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hpR
    linarith only [h, Real.log_three_gt_d9]
  have hcut := Real.log_nonneg (show (1 : ℝ) ≤ (99 / 40 : ℝ) * x by nlinarith only [hx])
  have hdiv : Real.log ((99 / 40 : ℝ) * x) / Real.log p ≤ Real.log ((99 / 40 : ℝ) * x) := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hlp)).mpr
    nlinarith only [hcut, hlp]
  exact div_le_div_of_nonneg_right (add_le_add hdiv le_rfl) (Real.sqrt_nonneg x)

/-- Input: an odd prime and x>=1. Claim: its combined square cost is at
most twice the variable conductor coefficient. Retain the existing odd Euler
certificates and variable ramp. Role: enable absorption at arbitrary scales. -/
theorem gamma_odd_prime_square_cost_le_variable {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x : ℝ}
    (hx : 1 ≤ x) : gammaSquareCombinedCost p x ≤ 2 * gammaVariableSquareMass x := by
  have he : 2 * gammaPrimeOddEulerCost p ≤ (19 / 25 : ℝ) := by
    by_cases hlarge : 11 ≤ p
    · exact (gamma_large_prime_odd_cost_le (by exact_mod_cast hlarge)).trans (by norm_num only)
    · have hfinite : ∀ q ∈ Finset.range 11, q.Prime → 3 ≤ q → q ∈ ([3, 5, 7] : List ℕ) := by
        decide +kernel
      exact
        gamma_small_prime_odd_cost_le
          (hfinite p (Finset.mem_range.mpr (lt_of_not_ge hlarge)) hp hp3)
  have hr := gamma_odd_prime_log_ramp_le_variable hp3 hx
  have hc :=
    gamma_square_combined_cost_le_log (lt_of_lt_of_le (by norm_num only : (1 : ℕ) < 3) hp3) hx
  have hm : (19 / 25 + gammaVariableRampAllowance x) / 2 ≤ gammaVariableSquareMass x :=
    le_max_right _ _
  linarith only [he, hr, hc, hm]

/-- Input: odd n, selected minus-one prime factors, arbitrary power prefixes
and x>=1. Claim: their actual total cost is at most twice the variable mass
times their logarithmic weight. Role: supply both conductor absorptions. -/
theorem gamma_actual_square_sum_le_variable {n f : ℕ} (hn : Odd n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (∑ p ∈ S, Real.log p) * (2 * gammaVariableSquareMass x) := by
  have hpoint :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      ∑ p ∈ S, Real.log p * (2 * gammaVariableSquareMass x) := by
    apply Finset.sum_le_sum
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (hS hp)
    have hpne : p ≠ 2 := fun he ↦ hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hS hp))
    have hp3 : 3 ≤ p := Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm hpne))
    exact
      (gamma_actual_minus_one_prime_cost_le χ hprime (hχ p hp) (K p)
            (zero_lt_one.trans_le hx)).trans
        (mul_le_mul_of_nonneg_left (gamma_odd_prime_square_cost_le_variable hprime hp3 hx)
          (Real.log_natCast_nonneg p))
  simpa only [Finset.sum_mul] using hpoint

/-- Input: n=d*t² odd, d dividing a positive f<=4d, minus-one input primes,
and x>=1. Claim: conductor and square losses fit the variable mass times
log(4n). Enlarge the conductor term and use the exact logarithmic gap.
Role: remove the fixed scale gate from the even-conductor branch. -/
theorem gamma_actual_square_absorbed_variable {n d t f : ℕ} (hn : n = d * t ^ 2) (hodd : Odd n)
    (hd : 0 < d) (ht : 0 < t) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      gammaVariableSquareMass x * Real.log (4 * (n : ℝ)) := by
  have hs := gamma_actual_square_sum_le_variable hodd S hS χ hχ K hx
  have hg :=
    gamma_square_only_prime_log_gap_budget hn hd ht hf hdf hfd S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hm := gamma_variable_square_mass_ge x
  have hm0 : 0 ≤ gammaVariableSquareMass x := by linarith only [hm]
  have hw := mul_le_mul_of_nonneg_left hg hm0
  have hf0 : 0 ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  have hf' := mul_le_mul_of_nonneg_right hm hf0
  nlinarith only [hs, hw, hf']

/-- Input: n=f*t² odd, positive f,t, selected minus-one primes and x>=1.
Claim: conductor and square costs fit variable mass times log(n), leaving
its log(4) allowance for two. Role: preserve the odd-conductor branch. -/
theorem gamma_actual_odd_square_absorbed_variable {n t f : ℕ} (hn : n = f * t ^ 2) (hodd : Odd n)
    (hf : 0 < f) (ht : 0 < t) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      gammaVariableSquareMass x * Real.log n := by
  have hs := gamma_actual_square_sum_le_variable hodd S hS χ hχ K hx
  have hg :=
    gamma_odd_conductor_square_log_budget hn hf ht S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hm := gamma_variable_square_mass_ge x
  have hm0 : 0 ≤ gammaVariableSquareMass x := by linarith only [hm]
  have hw := mul_le_mul_of_nonneg_left hg hm0
  have hf' := mul_le_mul_of_nonneg_right hm (Real.log_natCast_nonneg f)
  nlinarith only [hs, hw, hf']

/-- Input: x>=1. Claim: the weighted minus-one ramp at two is bounded by
its scale-dependent allowance. Cancel log two in the cutoff count and retain
the logarithmic numerator. Role: avoid imposing a fixed scale entrance. -/
theorem gamma_dyadic_minus_one_ramp_le_variable {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      gammaVariableRampAllowance x := by
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
  exact hw.trans (div_le_div_of_nonneg_right (add_le_add le_rfl hl1) (Real.sqrt_nonneg x))

/-- Input: value minus one at two, any positive-power prefix and x>=1.
Claim: after subtracting the kernel mass times log four, the actual cost is
at most 3/10 plus the ramp allowance. Role: support odd-conductor absorption. -/
theorem gamma_actual_dyadic_minus_one_cost_variable {f : ℕ} (χ : DirichletCharacter ℂ f)
    (hχ : χ 2 = -1) (K : Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    gammaActualPrimeLocalCost χ 2 K x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤
      3 / 10 + gammaVariableRampAllowance x := by
  have he := gamma_minus_one_positive_prime_correction_le_cost χ Nat.prime_two hχ K
  have hr := gamma_dyadic_minus_one_ramp_le_variable hx
  have hc := gamma_dyadic_weighted_euler_bounds.2
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [gammaActualPrimeLocalCost]
  rw [show χ ((2 : ℕ) : ZMod f) = -1 by simpa only [Nat.cast_ofNat] using hχ]
  norm_num only [Nat.cast_ofNat]
  linarith only [he, hr, hc]

/-- Input: x>=1. Claim: the weighted zero-branch ramp at two is bounded
by the scale-dependent allowance. Cancel log two in the cutoff count.
Role: retain the ramified dyadic error without a fixed scale entrance. -/
theorem gamma_dyadic_zero_ramp_le_variable {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      gammaVariableRampAllowance x := by
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
  have hmono :=
    div_le_div_of_nonneg_right
      (show Real.log ((99 / 40 : ℝ) * x) ≤ Real.log ((99 / 40 : ℝ) * x) + 1 by linarith only)
      (Real.sqrt_nonneg x)
  exact hw.trans hmono

/-- Input: value zero at two, any positive-power prefix and x>=1.
Claim: the actual cost is bounded by the variable dyadic allowance.
Proof: add the certified Euler bound to the ramp error.
Role: supply the even-conductor branch at arbitrary scales. -/
theorem gamma_actual_dyadic_zero_cost_variable {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = 0)
    (K : Finset ℕ) {x : ℝ} (hx : 1 ≤ x) :
    gammaActualPrimeLocalCost χ 2 K x ≤ gammaVariableDyadicAllowance x := by
  have he := sum_gammaResolventMangoldtWeight_primePowers_le_cost Nat.prime_two K
  have hr := gamma_dyadic_zero_ramp_le_variable hx
  have hc := gamma_dyadic_weighted_euler_bounds.1
  norm_num only [Nat.cast_ofNat] at he
  dsimp only [gammaActualPrimeLocalCost, gammaVariableDyadicAllowance]
  simp only [Nat.cast_ofNat, map_pow, hχ, zero_pow (Nat.succ_ne_zero _), Complex.zero_re, sub_zero,
    one_mul]
  linarith only [he, hr, hc]

/-- Input: x>=4096. Claim: the variable square coefficient equals the kernel
mass. Proof: the existing one-sixth ramp estimate makes the second maximum
branch smaller. Role: recover the original conductor coefficient at larger scales. -/
theorem gamma_variable_square_mass_eq_of_large_scale {x : ℝ} (hx : 4096 ≤ x) :
    gammaVariableSquareMass x = (11783423 / 25000000 : ℝ) := by
  have hr := gamma_cutoff_log_ramp_le_sixth hx
  apply max_eq_left
  change gammaVariableRampAllowance x ≤ (1 / 6 : ℝ) at hr
  linarith only [hr]

/-- Input: x>=4096. Claim: the variable dyadic allowance saves at least
149/10000 against the former 13/15 bound. Proof: retain the one-sixth estimate
without rounding up the Euler constant. Role: quantify a strict local improvement. -/
theorem gamma_variable_dyadic_allowance_gain {x : ℝ} (hx : 4096 ≤ x) :
    gammaVariableDyadicAllowance x + 149 / 10000 ≤ (13 / 15 : ℝ) := by
  have hr := gamma_cutoff_log_ramp_le_sixth hx
  dsimp only [gammaVariableDyadicAllowance, gammaVariableRampAllowance]
  linarith only [hr]

end PseudoPrime.Analysis
