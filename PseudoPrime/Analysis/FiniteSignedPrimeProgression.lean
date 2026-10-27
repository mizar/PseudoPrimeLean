/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPrimePowerCosts
public import PseudoPrime.Analysis.SignedResolventEulerBounds

/-! # Signed Euler costs along arbitrary prime-power progressions -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a nonnegative base, real exponent, and natural progression indices.
Claim: the node at exponent d*k+r equals a geometric progression with ratio raised to d.
Proof: commute real and natural powers before distributing the exponent.
Role: share positive-power and odd-power local formulas. -/
theorem signed_euler_progression_node_eq {p σ : ℝ} (hp : 0 ≤ p) (d r k : ℕ) :
    (p ^ (d * k + r)) ^ (-σ) = ((p ^ (-σ)) ^ d) ^ k * (p ^ (-σ)) ^ r := by
  rw [gamma_euler_power_eq_geometric hp, pow_add, pow_mul]

/-- Input: a base above one, positive exponent, positive step, and any natural offset.
Claim: the node progression is summable.
Proof: its geometric ratio lies in [0,1).
Role: justify finite signed coefficient interchange before local bounds. -/
theorem summable_signed_euler_progression_node {p σ : ℝ} (hp : 1 < p) (hσ : 0 < σ) {d : ℕ}
    (hd : 0 < d) (r : ℕ) : Summable (fun k : ℕ ↦ (p ^ (d * k + r)) ^ (-σ)) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hr0 := Real.rpow_nonneg hp0 (-σ)
  have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hσ)
  have h :=
    (summable_geometric_of_lt_one (pow_nonneg hr0 d) (pow_lt_one₀ hr0 hr1 hd.ne')).mul_right
      ((p ^ (-σ)) ^ r)
  exact h.congr (fun k ↦ by rw [signed_euler_progression_node_eq hp0])

/-- Input: the geometric progression hypotheses.
Claim: the full node sum is ratio^r/(1-ratio^d).
Proof: evaluate the convergent geometric series.
Role: keep exact parity and arithmetic-progression cancellations. -/
theorem tsum_signed_euler_progression_node {p σ : ℝ} (hp : 1 < p) (hσ : 0 < σ) {d : ℕ} (hd : 0 < d)
    (r : ℕ) : (∑' k : ℕ, (p ^ (d * k + r)) ^ (-σ)) = (p ^ (-σ)) ^ r / (1 - (p ^ (-σ)) ^ d) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hr0 := Real.rpow_nonneg hp0 (-σ)
  have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hσ)
  simp_rw [signed_euler_progression_node_eq hp0]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (pow_nonneg hr0 d) (pow_lt_one₀ hr0 hr1 hd.ne')]
  rw [div_eq_mul_inv, mul_comm]

/-- Input: rational node-coefficient pairs, a real base, and a step and offset.
Output: the signed finite geometric-cost sum, without absolute coefficient values.
Role: evaluate positive or odd prime-power costs for arbitrary candidate kernels. -/
noncomputable def finiteSignedPrimeProgressionCost (l : List (ℚ × ℚ)) (p : ℝ) (d r : ℕ) : ℝ :=
  (l.map
      (fun ab ↦
        (ab.2 : ℝ) *
          ((p ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ r / (1 - (p ^ (-(1 / 2 + (ab.1 : ℝ)))) ^ d)))).sum

/-- Input: positive node exponents and a positive-step progression at a base above one.
Claim: the signed Euler weight is summable along the progression.
Proof: each node is summable and the coefficient list is finite.
Role: establish convergence without discarding coefficient cancellation. -/
theorem summable_finiteSignedEulerWeight_progression (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ)) {p : ℝ} (hp : 1 < p) {d : ℕ} (hd : 0 < d)
    (r : ℕ) : Summable (fun k : ℕ ↦ finiteSignedEulerWeight l (p ^ (d * k + r))) := by
  apply summable_list_sum l (fun ab k ↦ (ab.2 : ℝ) * (p ^ (d * k + r)) ^ (-(1 / 2 + (ab.1 : ℝ))))
  intro ab hab
  exact (summable_signed_euler_progression_node hp (ha ab hab) hd r).mul_left (ab.2 : ℝ)

/-- Input: positive node exponents and a convergent progression.
Claim: its exact signed Euler sum equals the finite progression cost.
Proof: commute the finite coefficient sum with the infinite sum and evaluate each node.
Role: support numerical interval certificates for new phase kernels. -/
theorem tsum_finiteSignedEulerWeight_progression_eq_cost (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ)) {p : ℝ} (hp : 1 < p) {d : ℕ} (hd : 0 < d)
    (r : ℕ) :
    (∑' k : ℕ, finiteSignedEulerWeight l (p ^ (d * k + r))) =
      finiteSignedPrimeProgressionCost l p d r := by
  have hs (ab : ℚ × ℚ) (hab : ab ∈ l) :
    Summable (fun k : ℕ ↦ (ab.2 : ℝ) * (p ^ (d * k + r)) ^ (-(1 / 2 + (ab.1 : ℝ)))) :=
    (summable_signed_euler_progression_node hp (ha ab hab) hd r).mul_left (ab.2 : ℝ)
  change
    (∑' k : ℕ, (l.map (fun ab ↦ (ab.2 : ℝ) * (p ^ (d * k + r)) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum) = _
  rw [tsum_list_sum l _ hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  rw [tsum_mul_left, tsum_signed_euler_progression_node hp (ha ab hab) hd r]

/-- Input: nonnegative combined Euler weight and the progression hypotheses.
Claim: any finite progression prefix is at most the exact signed full cost.
Proof: enlarge only the nonnegative combined terms, after signed coefficients are combined.
Role: avoid an absolute-coefficient envelope for finite local losses. -/
theorem sum_finiteSignedEulerWeight_progression_le_cost (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) {p : ℝ} (hp : 1 < p) {d : ℕ}
    (hd : 0 < d) (r : ℕ) (K : Finset ℕ) :
    (∑ k ∈ K, finiteSignedEulerWeight l (p ^ (d * k + r))) ≤
      finiteSignedPrimeProgressionCost l p d r := by
  rw [← tsum_finiteSignedEulerWeight_progression_eq_cost l ha hp hd r]
  exact
    (summable_finiteSignedEulerWeight_progression l ha hp hd r).sum_le_tsum K
      (fun k _ ↦ hW _ (one_le_pow₀ hp.le))

/-- Input: a prime, positive step and offset, and a nonnegative combined Euler weight.
Claim: a finite Mangoldt progression prefix is bounded by log(p) times the exact cost.
Proof: Mangoldt is log(p) on positive prime powers and the finite Euler bound applies.
Role: connect arbitrary signed candidates to actual prime-local corrections. -/
theorem sum_finiteSignedMangoldtWeight_progression_le_cost (l : List (ℚ × ℚ))
    (ha : ∀ ab ∈ l, 0 < (1 / 2 : ℝ) + (ab.1 : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ finiteSignedEulerWeight l u) {p : ℕ} (hp : p.Prime) {d r : ℕ}
    (hd : 0 < d) (hr : 0 < r) (K : Finset ℕ) :
    (∑ k ∈ K, finiteSignedMangoldtWeight l (p ^ (d * k + r))) ≤
      Real.log p * finiteSignedPrimeProgressionCost l p d r := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [finiteSignedMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt (Nat.add_pos_right _ hr)),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
  rw [← Finset.mul_sum]
  exact
    mul_le_mul_of_nonneg_left (sum_finiteSignedEulerWeight_progression_le_cost l ha hW hp1 hd r K)
      (Real.log_nonneg hp1.le)

end PseudoPrime.Analysis
