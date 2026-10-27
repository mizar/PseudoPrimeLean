/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import PseudoPrime.Analysis.ListInfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Exact geometric Euler costs at prime powers -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On a nonnegative real base, a power of a natural power with real exponent
is the corresponding natural power of the real power. This transfers each
resolvent Euler node at p^k to its geometric ratio without changing signs. -/
theorem gamma_euler_power_eq_geometric {p : ℝ} (hp : 0 ≤ p) (σ : ℝ) (k : ℕ) :
    (p ^ k) ^ (-σ) = (p ^ (-σ)) ^ k := by
  rw [← Real.rpow_natCast_mul hp k (-σ), mul_comm (k : ℝ) (-σ), Real.rpow_mul_natCast hp (-σ) k]

/-- For a base greater than one and positive exponent, the positive-power
Euler node is summable. Its geometric ratio lies in [0,1). This supplies the
absolute convergence required before combining the signed local node costs. -/
theorem summable_gamma_euler_positive_powers {p σ : ℝ} (hp : 1 < p) (hσ : 0 < σ) :
    Summable (fun k : ℕ ↦ (p ^ (k + 1)) ^ (-σ)) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hr0 := Real.rpow_nonneg hp0 (-σ)
  have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hσ)
  have h := (summable_geometric_of_lt_one hr0 hr1).mul_right (p ^ (-σ))
  exact h.congr (fun k ↦ by rw [gamma_euler_power_eq_geometric hp0, pow_succ])

/-- For a base greater than one and positive exponent, the positive-power
node sums to its geometric ratio divided by one minus that ratio. This exact
formula evaluates each signed Euler contribution to the ramified prime cost. -/
theorem tsum_gamma_euler_positive_powers {p σ : ℝ} (hp : 1 < p) (hσ : 0 < σ) :
    (∑' k : ℕ, (p ^ (k + 1)) ^ (-σ)) = p ^ (-σ) / (1 - p ^ (-σ)) := by
  have hp0 : 0 ≤ p := (zero_lt_one.trans hp).le
  have hr0 := Real.rpow_nonneg hp0 (-σ)
  have hr1 := Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hσ)
  simp_rw [gamma_euler_power_eq_geometric hp0]
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
  rw [div_eq_mul_inv, mul_comm]

/-- The actual signed Gamma Euler weight is summable over all positive powers
of a base greater than one. Each certified node has a positive exponent,
and summability survives the finite signed combination. This justifies the
exact local-cost sum without replacing coefficients by their absolute values. -/
theorem summable_gammaResolventEulerWeight_powers {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ ↦ gammaResolventEulerWeight (p ^ (k + 1))) := by
  apply
    summable_list_sum gammaResolventCoefficients
      (fun ab k ↦ (ab.2 : ℝ) * (p ^ (k + 1)) ^ (-(1 / 2 + (ab.1 : ℝ))))
  intro ab hab
  have ha := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
  have har : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
  norm_num only at har
  have hσ : 0 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by linarith only [har]
  exact (summable_gamma_euler_positive_powers hp hσ).mul_left (ab.2 : ℝ)

/-- Closed signed Euler cost for one base p: each resolvent node contributes
its coefficient times the positive-power geometric sum. For p > 1 this is
the exact sum of H(p^k), k >= 1, used in the ramified local budget. -/
noncomputable def gammaPrimeEulerCost (p : ℝ) : ℝ :=
  (gammaResolventCoefficients.map
      (fun ab ↦ (ab.2 : ℝ) * (p ^ (-(1 / 2 + (ab.1 : ℝ))) / (1 - p ^ (-(1 / 2 + (ab.1 : ℝ))))))).sum

/-- For every real base greater than one, the positive-power sum of the actual
Euler weight equals the closed signed prime cost. Absolute convergence permits
the finite-infinite interchange, after which each node uses the geometric
formula. This is an exact identity for local-cost evaluation. -/
theorem tsum_gammaResolventEulerWeight_powers_eq_cost {p : ℝ} (hp : 1 < p) :
    (∑' k : ℕ, gammaResolventEulerWeight (p ^ (k + 1))) = gammaPrimeEulerCost p := by
  have hs (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) :
    Summable (fun k : ℕ ↦ (ab.2 : ℝ) * (p ^ (k + 1)) ^ (-(1 / 2 + (ab.1 : ℝ)))) := by
    have ha := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
    have har : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
    norm_num only at har
    exact
      (summable_gamma_euler_positive_powers hp
            (by linarith only [har] : (0 : ℝ) < 1 / 2 + (ab.1 : ℝ))).mul_left
        (ab.2 : ℝ)
  change
    (∑' k : ℕ,
        (gammaResolventCoefficients.map
            (fun ab ↦ (ab.2 : ℝ) * (p ^ (k + 1)) ^ (-(1 / 2 + (ab.1 : ℝ))))).sum) =
      _
  rw [tsum_list_sum gammaResolventCoefficients _ hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  have ha := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
  have har : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
  norm_num only at har
  rw [tsum_mul_left,
    tsum_gamma_euler_positive_powers hp (by linarith only [har] : (0 : ℝ) < 1 / 2 + (ab.1 : ℝ))]

/-- A finite set of positive powers contributes at most the full signed Euler
cost for a base greater than one. The actual weight is nonnegative on these
powers and its full series is summable. This is the local bound used to enlarge
a finite ramified prefix to all positive powers of each conductor prime. -/
theorem sum_gammaResolventEulerWeight_powers_le_cost {p : ℝ} (hp : 1 < p) (K : Finset ℕ) :
    (∑ k ∈ K, gammaResolventEulerWeight (p ^ (k + 1))) ≤ gammaPrimeEulerCost p := by
  rw [← tsum_gammaResolventEulerWeight_powers_eq_cost hp]
  exact
    (summable_gammaResolventEulerWeight_powers hp).sum_le_tsum K
      (fun k hk ↦ gamma_resolvent_euler_weight_nonneg (one_le_pow₀ hp.le))

/-- For a prime and any finite set of positive exponents, the actual Mangoldt
Euler weights sum to at most log p times the closed signed Euler cost.
Mangoldt is exactly log p on those powers; combine the finite-power bound
with its nonnegative logarithm. This is the ramified prefix local-cost input. -/
theorem sum_gammaResolventMangoldtWeight_primePowers_le_cost {p : ℕ} (hp : p.Prime) (K : Finset ℕ) :
    (∑ k ∈ K, gammaResolventMangoldtWeight (p ^ (k + 1))) ≤ Real.log p * gammaPrimeEulerCost p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [gammaResolventMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
  rw [← Finset.mul_sum]
  exact
    mul_le_mul_of_nonneg_left (sum_gammaResolventEulerWeight_powers_le_cost hp1 K)
      (Real.log_nonneg hp1.le)

/-- For a finite prime set with a common logarithmic budget, the actual finite
Euler prime-power losses and ramp losses satisfy one joint dual-cap bound.
Enlarge each Euler prefix to its exact geometric cost, then combine it with
the ramp cost before applying the budget. This connects actual prefix terms
to the common local allowance without charging the conductor twice. -/
theorem gamma_primePower_joint_cost_le_dual_cap (S : Finset ℕ) (K : ℕ → Finset ℕ) (Ramp : ℕ → ℝ)
    {μ L : ℝ} (hμ : 0 ≤ μ) (hprime : ∀ p ∈ S, p.Prime) (hbudget : ∑ p ∈ S, Real.log p ≤ L) :
    (∑ p ∈ S, ((∑ k ∈ K p, gammaResolventMangoldtWeight (p ^ (k + 1))) + Real.log p * Ramp p)) ≤
      μ * L + ∑ p ∈ S, Real.log p * max (gammaPrimeEulerCost p + Ramp p - μ) 0 := by
  have hpoint :
    (∑ p ∈ S, ((∑ k ∈ K p, gammaResolventMangoldtWeight (p ^ (k + 1))) + Real.log p * Ramp p)) ≤
      ∑ p ∈ S, Real.log p * (gammaPrimeEulerCost p + Ramp p) := by
    apply Finset.sum_le_sum
    intro p hp
    rw [mul_add]
    exact
      add_le_add (sum_gammaResolventMangoldtWeight_primePowers_le_cost (hprime p hp) (K p)) le_rfl
  have hlog (p : ℕ) (hp : p ∈ S) : 0 ≤ Real.log p := by
    have h : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).one_le
    exact Real.log_nonneg h
  exact
    hpoint.trans
      (ramified_joint_cost_le_dual_cap S (fun p ↦ Real.log p) (fun p ↦ gammaPrimeEulerCost p) Ramp
        hμ hlog hbudget)

end PseudoPrime.Analysis
