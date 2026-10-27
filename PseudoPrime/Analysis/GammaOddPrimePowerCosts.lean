/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaConductorBudget

/-! # Exact odd-prime-power Euler costs for the square-part comparison -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On a nonnegative base, an odd natural power at a real Euler exponent
equals the odd geometric term. The squared ratio gives the geometric decay
for the character value minus one, where even powers retain value plus one. -/
theorem gamma_euler_odd_power_eq_geometric {p : ℝ} (hp : 0 ≤ p) (σ : ℝ) (k : ℕ) :
    (p ^ (2 * k + 1)) ^ (-σ) = ((p ^ (-σ)) ^ 2) ^ k * p ^ (-σ) := by
  rw [gamma_euler_power_eq_geometric hp, pow_add, pow_mul, pow_one]

/-- For a base greater than one and positive Euler exponent, the odd-power
node series is summable with squared geometric ratio. This establishes the
convergence needed to evaluate the signed square-part cost. -/
theorem summable_gamma_euler_odd_powers {p σ : ℝ} (hp : 1 < p) (hσ : 0 < σ) :
    Summable (fun k : ℕ ↦ (p ^ (2 * k + 1)) ^ (-σ)) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hr0 := Real.rpow_nonneg hp0 (-σ)
  have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hσ)
  have h :=
    (summable_geometric_of_lt_one (sq_nonneg (p ^ (-σ)))
          (pow_lt_one₀ hr0 hr1 (by norm_num only : (2 : ℕ) ≠ 0))).mul_right
      (p ^ (-σ))
  exact h.congr (fun k ↦ by rw [gamma_euler_odd_power_eq_geometric hp0])

/-- The odd-power Euler node sums exactly to r/(1-r^2), where r=p^(-sigma).
The squared ratio is below one. This is the signed coefficient formula
used for the character value minus one in the square-part local loss. -/
theorem tsum_gamma_euler_odd_powers {p σ : ℝ} (hp : 1 < p) (hσ : 0 < σ) :
    (∑' k : ℕ, (p ^ (2 * k + 1)) ^ (-σ)) = p ^ (-σ) / (1 - (p ^ (-σ)) ^ 2) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hr0 := Real.rpow_nonneg hp0 (-σ)
  have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hσ)
  simp_rw [gamma_euler_odd_power_eq_geometric hp0]
  rw [tsum_mul_right,
    tsum_geometric_of_lt_one (sq_nonneg (p ^ (-σ)))
      (pow_lt_one₀ hr0 hr1 (by norm_num only : (2 : ℕ) ≠ 0))]
  rw [div_eq_mul_inv, mul_comm]

/-- The actual signed Euler weight is summable over odd positive powers.
Each certified node has a positive exponent, and the finite signed sum retains
absolute convergence. This permits exact odd-power local-cost evaluation. -/
theorem summable_gammaResolventEulerWeight_odd_powers {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ ↦ gammaResolventEulerWeight (p ^ (2 * k + 1))) := by
  apply
    summable_list_sum gammaResolventCoefficients
      (fun ab k ↦ (ab.2 : ℝ) * (p ^ (2 * k + 1)) ^ (-(1 / 2 + (ab.1 : ℝ))))
  intro ab hab
  have ha := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
  have har : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
  norm_num only at har
  have hσ : 0 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by linarith only [har]
  exact (summable_gamma_euler_odd_powers hp hσ).mul_left (ab.2 : ℝ)

/-- Closed signed odd-power Euler cost for one base. Each node has ratio
r=p^(-(1/2+a)) and contributes b*r/(1-r^2). The square-part comparison
uses twice this cost when the local quadratic character value is minus one. -/
noncomputable def gammaPrimeOddEulerCost (p : ℝ) : ℝ :=
  (gammaResolventCoefficients.map
      (fun ab ↦
        (ab.2 : ℝ) * (p ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - (p ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ 2)))).sum

/-- For a base greater than one, the actual odd-power Euler series equals its
closed signed local cost. Absolute convergence permits the finite coefficient
sum to pass through the infinite sum before evaluating the geometric nodes. -/
theorem tsum_gammaResolventEulerWeight_odd_powers_eq_cost {p : ℝ} (hp : 1 < p) :
    (∑' k : ℕ, gammaResolventEulerWeight (p ^ (2 * k + 1))) = gammaPrimeOddEulerCost p := by
  have hs (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) :
    Summable (fun k : ℕ ↦ (ab.2 : ℝ) * (p ^ (2 * k + 1)) ^ (-(1 / 2 + (ab.1 : ℝ)))) := by
    have ha := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
    have har : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
    norm_num only at har
    exact
      (summable_gamma_euler_odd_powers hp
            (by linarith only [har] : (0 : ℝ) < 1 / 2 + (ab.1 : ℝ))).mul_left
        (ab.2 : ℝ)
  change
    (∑' k : ℕ,
        (gammaResolventCoefficients.map
            (fun ab ↦ (ab.2 : ℝ) * (p ^ (2 * k + 1)) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum) =
      _
  rw [tsum_list_sum gammaResolventCoefficients _ hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  have ha := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
  have har : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
  norm_num only at har
  rw [tsum_mul_left,
    tsum_gamma_euler_odd_powers hp (by linarith only [har] : (0 : ℝ) < 1 / 2 + (ab.1 : ℝ))]

/-- A finite set of odd positive powers contributes at most the full signed
odd-power Euler cost. Use nonnegativity of the actual weight and summability
to enlarge the finite sum. This preserves the even-power cancellation in the
square-part comparison rather than bounding all powers together. -/
theorem sum_gammaResolventEulerWeight_odd_powers_le_cost {p : ℝ} (hp : 1 < p) (K : Finset ℕ) :
    (∑ k ∈ K, gammaResolventEulerWeight (p ^ (2 * k + 1))) ≤ gammaPrimeOddEulerCost p := by
  rw [← tsum_gammaResolventEulerWeight_odd_powers_eq_cost hp]
  exact
    (summable_gammaResolventEulerWeight_odd_powers hp).sum_le_tsum K
      (fun k hk ↦ gamma_resolvent_euler_weight_nonneg (one_le_pow₀ hp.le))

/-- For a prime, the finite Mangoldt sum over odd positive powers is bounded
by log p times the exact odd-power cost. Mangoldt is log p on each positive
prime power, and the logarithm is nonnegative. This supplies the local bound
before doubling the character-minus-one loss. -/
theorem sum_gammaResolventMangoldtWeight_odd_primePowers_le_cost {p : ℕ} (hp : p.Prime)
    (K : Finset ℕ) :
    (∑ k ∈ K, gammaResolventMangoldtWeight (p ^ (2 * k + 1))) ≤
      Real.log p * gammaPrimeOddEulerCost p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [gammaResolventMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
  rw [← Finset.mul_sum]
  exact
    mul_le_mul_of_nonneg_left (sum_gammaResolventEulerWeight_odd_powers_le_cost hp1 K)
      (Real.log_nonneg hp1.le)

/-- If a character has value minus one at p, its Euler correction vanishes
at even powers and is twice the weight at odd powers. Character multiplicativity
and the powers of minus one prove both identities. This connects the odd-power
cost to the actual local character correction while retaining the even terms. -/
theorem gamma_character_minus_one_power_corrections {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ p = -1) (k : ℕ) :
    (1 - (χ (p ^ (2 * k))).re) * gammaResolventMangoldtWeight (p ^ (2 * k)) = 0 ∧
      (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1)) =
        2 * gammaResolventMangoldtWeight (p ^ (2 * k + 1)) := by
  norm_num only [Nat.cast_pow, map_pow, map_mul, hχ, pow_add, pow_mul, pow_one, one_pow, one_mul,
    true_and, Complex.one_re, Complex.neg_re, sub_self, zero_mul]

/-- If a character has value minus one at a prime, its actual finite odd-power
correction is at most twice log p times the exact odd Euler cost. Apply the
power correction identity before the finite cost bound. This is the Euler
part of the square-prime local loss, ready to combine with its odd ramp cost. -/
theorem gamma_minus_one_odd_prime_correction_le_cost {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hχ : χ p = -1) (K : Finset ℕ) :
    (∑ k ∈ K, (1 - (χ (p ^ (2 * k + 1))).re) * gammaResolventMangoldtWeight (p ^ (2 * k + 1))) ≤
      2 * (Real.log p * gammaPrimeOddEulerCost p) := by
  rw [Finset.sum_congr rfl (fun k hk ↦ (gamma_character_minus_one_power_corrections χ hχ k).2), ←
    Finset.mul_sum]
  exact
    mul_le_mul_of_nonneg_left (sum_gammaResolventMangoldtWeight_odd_primePowers_le_cost hp K)
      (by norm_num only : (0 : ℝ) ≤ 2)

end PseudoPrime.Analysis
