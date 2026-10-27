/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PowerSeriesCoefficientBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PowerSums
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Polynomial.Fourier
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
public import Mathlib.Topology.Algebra.Polynomial

/-! # Formal-series Newton interpolation for reciprocal powers -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: two nonzero complex nodes, represented as units.

Claim: the reciprocal formal series satisfy the resolvent identity.

Proof: insert the two inverse identities and rearrange in the power-series ring.

Role: supplies the Newton expansion step without dividing by the difference of two nodes.
-/
theorem reciprocalSeries_resolvent (x z : ℂˣ) :
    PowerSeries.invUnitsSub x =
      PowerSeries.invUnitsSub z +
        PowerSeries.C ((z : ℂ) - x) * PowerSeries.invUnitsSub z * PowerSeries.invUnitsSub x := by
  have h :
    PowerSeries.invUnitsSub x - PowerSeries.invUnitsSub z =
      PowerSeries.C ((z : ℂ) - x) * PowerSeries.invUnitsSub z * PowerSeries.invUnitsSub x := by
    calc
      _ =
          PowerSeries.invUnitsSub x *
              (PowerSeries.invUnitsSub z * (PowerSeries.C (z : ℂ) - PowerSeries.X)) -
            PowerSeries.invUnitsSub z *
              (PowerSeries.invUnitsSub x * (PowerSeries.C (x : ℂ) - PowerSeries.X)) :=
        by rw [PowerSeries.invUnitsSub_mul_sub, PowerSeries.invUnitsSub_mul_sub, mul_one, mul_one]
      _ = _ := by
        rw [map_sub]; ring
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/--
Inputs: a sequence of nonzero complex nodes, a nonzero evaluation point, and a finite length.

Claim: its reciprocal series is the finite Newton expansion plus a factored remainder.
Nodes may repeat.

Proof: induct on the length using the resolvent identity; no difference of nodes is inverted.

Role: gives exact interpolation when the evaluation point is one of the selected nodes.
-/
theorem reciprocalSeries_newton_expansion (z : ℕ → ℂˣ) (x : ℂˣ) (n : ℕ) :
    PowerSeries.invUnitsSub x =
      (∑ k ∈ Finset.range n,
          (∏ i ∈ Finset.range k, PowerSeries.C ((z i : ℂ) - x)) *
            (∏ i ∈ Finset.range (k + 1), PowerSeries.invUnitsSub (z i))) +
        (∏ i ∈ Finset.range n, PowerSeries.C ((z i : ℂ) - x)) *
          (∏ i ∈ Finset.range n, PowerSeries.invUnitsSub (z i)) *
          PowerSeries.invUnitsSub x := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Finset.prod_empty, one_mul, zero_add]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    conv_lhs => rw [ih]
    have h := reciprocalSeries_resolvent x (z n)
    linear_combination
      (∏ i ∈ Finset.range n, PowerSeries.C ((z i : ℂ) - x)) *
        (∏ i ∈ Finset.range n, PowerSeries.invUnitsSub (z i)) *
        h

/--
Inputs: a nonzero complex node and a coefficient index.

Claim: the normalized reciprocal-series coefficient is the corresponding inverse power.

Proof: evaluate its coefficient and cancel the nonzero node.

Role: identifies the generating series for complete homogeneous expressions in inverse nodes.
-/
theorem normalizedReciprocalSeries_coeff (u : ℂˣ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.C (u : ℂ) * PowerSeries.invUnitsSub u) = ((u : ℂ)⁻¹) ^ n := by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_invUnitsSub, one_divp, Units.val_inv_eq_inv_val]
  change (u : ℂ) * ((u : ℂ) ^ (n + 1))⁻¹ = _
  rw [pow_succ, mul_inv_rev, ← inv_pow, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero u), one_mul]

/--
Inputs: a nonzero complex node of norm at least one and a coefficient index.

Claim: the normalized reciprocal-series coefficient has norm at most one.

Proof: its inverse power has norm at most one.

Role: supplies the coefficientwise hypothesis for the finite-product binomial bound.
-/
theorem normalizedReciprocalSeries_coeff_norm_le_one (u : ℂˣ) (hu : (1 : ℝ) ≤ ‖(u : ℂ)‖) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.C (u : ℂ) * PowerSeries.invUnitsSub u)‖ ≤ 1 := by
  rw [normalizedReciprocalSeries_coeff, norm_pow, norm_inv]
  exact
    pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _))
      ((inv_le_one₀ (lt_of_lt_of_le zero_lt_one hu)).mpr hu)

/--
Inputs: a sequence of nonzero nodes of norm at least one on its first `k + 1` indices.

Claim: the coefficient at `M` of the product of normalized reciprocal series has norm at most
`choose (k + M) k`.

Proof: apply the coefficientwise geometric-series product bound.

Role: gives the required quantitative complete homogeneous coefficient bound for Newton
interpolation, also when nodes repeat.
-/
theorem normalizedReciprocalSeries_prod_coeff_norm_le_choose (z : ℕ → ℂˣ) (k M : ℕ)
    (hz : ∀ i < k + 1, (1 : ℝ) ≤ ‖(z i : ℂ)‖) :
    ‖PowerSeries.coeff M
          (∏ i ∈ Finset.range (k + 1), (PowerSeries.C (z i : ℂ) * PowerSeries.invUnitsSub (z i)))‖ ≤
      (Nat.choose (k + M) k : ℝ) := by
  exact
    PseudoPrime.Analysis.powerSeries_coeff_prod_norm_le_choose _ _ (Finset.card_range (k + 1))
      (fun i hi n ↦
        normalizedReciprocalSeries_coeff_norm_le_one (z i) (hz i (Finset.mem_range.mp hi)) n)
      M

/--
Inputs: a finite set of nonzero nodes and a coefficient index.

Claim: normalizing each reciprocal series multiplies the product coefficient by the product of
the nodes.

Proof: collect the constant series and apply the constant-multiple coefficient formula.

Role: cancels the node products against normalized Newton polynomial coefficients.
-/
theorem normalizedReciprocalSeries_prod_coeff {ι : Type} (s : Finset ι) (z : ι → ℂˣ) (M : ℕ) :
    PowerSeries.coeff M (∏ i ∈ s, (PowerSeries.C (z i : ℂ) * PowerSeries.invUnitsSub (z i))) =
      (∏ i ∈ s, (z i : ℂ)) * PowerSeries.coeff M (∏ i ∈ s, PowerSeries.invUnitsSub (z i)) := by
  rw [Finset.prod_mul_distrib, ← map_prod, PowerSeries.coeff_C_mul]

/--
Inputs: a sequence of nonzero nodes, a selected index below `n`, and an inverse-power order.

Claim: the reciprocal power at that node is a finite Newton expansion whose coefficients are
coefficients of products of reciprocal formal series. Repeated nodes are allowed.

Proof: the factored remainder vanishes at a selected node; take the coefficient at `M`.

Role: supplies the exact finite interpolation formula needed to compare a total weight with a
later block of weighted power sums.
-/
theorem inversePower_newton_interpolation (z : ℕ → ℂˣ) (n M j : ℕ) (hj : j < n) :
    ((z j : ℂ) ^ (M + 1))⁻¹ =
      ∑ k ∈ Finset.range n,
        (∏ i ∈ Finset.range k, ((z i : ℂ) - z j)) *
          PowerSeries.coeff M (∏ i ∈ Finset.range (k + 1), PowerSeries.invUnitsSub (z i)) := by
  have h := reciprocalSeries_newton_expansion z (z j) n
  have hp : (∏ i ∈ Finset.range n, PowerSeries.C ((z i : ℂ) - z j)) = (0 : PowerSeries ℂ) :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hj) (by rw [sub_self, map_zero])
  rw [hp, zero_mul, zero_mul, add_zero] at h
  have hc := congrArg (PowerSeries.coeff M) h
  simpa only [PowerSeries.coeff_invUnitsSub, one_divp, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val, map_sum, ← map_prod, PowerSeries.coeff_C_mul] using hc

/--
Inputs: a sequence of nonzero nodes and a prefix length `k`.

Definition: the polynomial `∏ i < k, (zᵢ - X)`, whose evaluation vanishes at each prefix node.

Role: is the polynomial factor in the finite Newton expansion.
-/
noncomputable def newtonRootPolynomial (z : ℕ → ℂˣ) (k : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range k, (Polynomial.C (z i : ℂ) - Polynomial.X)

/--
Inputs: a sequence of nonzero nodes, a prefix index `k`, and an inverse-power order `M`.

Definition: the coefficient at `M` in the product of the first `k + 1` reciprocal formal series.

Role: is the scalar coefficient multiplying the Newton root polynomial.
-/
noncomputable def reciprocalProductCoefficient (z : ℕ → ℂˣ) (k M : ℕ) : ℂ :=
  PowerSeries.coeff M (∏ i ∈ Finset.range (k + 1), PowerSeries.invUnitsSub (z i))

private theorem reverseRootPolynomial_coeff_norm {ι : Type} (s : Finset ι) (z : ι → ℂ) (l : ℕ) :
    ‖(∏ i ∈ s, (Polynomial.C (z i) - Polynomial.X)).coeff l‖ =
      ‖(∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))).coeff l‖ := by
  have h :
    (∏ i ∈ s, (Polynomial.C (z i) - Polynomial.X)) =
      Polynomial.C ((-1 : ℂ) ^ s.card) * (∏ i ∈ s, (Polynomial.X - Polynomial.C (z i))) := by
    calc
      _ = ∏ i ∈ s, Polynomial.C (-1 : ℂ) * (Polynomial.X - Polynomial.C (z i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [map_neg, map_one, neg_one_mul, neg_sub]
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_pow]
  rw [h, Polynomial.coeff_C_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

/--
Inputs: a prefix of nonzero nodes, an inverse-power order, and a polynomial coefficient index.

Claim: each Newton term coefficient factors into a normalized series coefficient and a
normalized polynomial coefficient.

Proof: collect the node product in the normalized series and cancel that nonzero product.

Role: makes the cancellation of large node norms explicit before applying the binomial bounds.
-/
theorem newton_term_coeff_eq_normalized (z : ℕ → ℂˣ) (k M l : ℕ) :
    reciprocalProductCoefficient z k M * (newtonRootPolynomial z k).coeff l =
      PowerSeries.coeff M
          (∏ i ∈ Finset.range (k + 1), (PowerSeries.C (z i : ℂ) * PowerSeries.invUnitsSub (z i))) *
        ((newtonRootPolynomial z k).coeff l / (∏ i ∈ Finset.range (k + 1), (z i : ℂ))) := by
  have hd : (∏ i ∈ Finset.range (k + 1), (z i : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi ↦ Units.ne_zero (z i))
  rw [normalizedReciprocalSeries_prod_coeff]
  dsimp only [reciprocalProductCoefficient]
  rw [mul_comm (∏ i ∈ Finset.range (k + 1), (z i : ℂ)), mul_assoc, ← mul_div_assoc,
    mul_div_cancel_left₀ _ hd]

/--
Inputs: nodes of norm at least one on the first `k + 1` indices, an inverse-power order `M`, and
a coefficient index `l ≤ k`.

Claim: the Newton term coefficient has norm at most `choose (k + M) k * choose k l`.

Proof: cancel the node products and apply the normalized series and polynomial bounds.

Role: controls the entire Newton term before summing the coefficients to obtain a power-sum
block estimate.
-/
theorem newton_term_coeff_norm_le_choose (z : ℕ → ℂˣ) (k M l : ℕ) (hl : l ≤ k)
    (hz : ∀ i < k + 1, (1 : ℝ) ≤ ‖(z i : ℂ)‖) :
    ‖reciprocalProductCoefficient z k M * (newtonRootPolynomial z k).coeff l‖ ≤
      (Nat.choose (k + M) k : ℝ) * (Nat.choose k l : ℝ) := by
  rw [newton_term_coeff_eq_normalized, norm_mul]
  apply mul_le_mul (normalizedReciprocalSeries_prod_coeff_norm_le_choose z k M hz)
  · rw [norm_div, newtonRootPolynomial, reverseRootPolynomial_coeff_norm]
    have h :=
      normalized_prod_X_sub_C_coeff_div_extra_norm_le_choose (Finset.range k) (fun i ↦ (z i : ℂ))
        (z k) (fun i hi ↦ hz i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
        (hz k (Nat.lt_succ_self k)) (by simpa only [Finset.card_range] using hl)
    rw [norm_div] at h
    simpa only [Finset.prod_range_succ, Finset.card_range] using h
  · exact norm_nonneg _
  · exact Nat.cast_nonneg _

/--
Inputs: a sequence of nodes and a prefix length.

Claim: the Newton root polynomial has degree below the successor of that length.

Proof: each linear factor has degree one, so the product degree is at most the length.

Role: permits a finite coefficient expansion of every Newton term.
-/
theorem newtonRootPolynomial_natDegree_lt (z : ℕ → ℂˣ) (k : ℕ) :
    (newtonRootPolynomial z k).natDegree < k + 1 := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, (Polynomial.C (z i : ℂ) - Polynomial.X).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = k := by
      simp only [← neg_sub Polynomial.X, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C,
        Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    _ < k + 1 := Nat.lt_succ_self k

/--
Inputs: a sequence of nonzero nodes, complex weights on its first `n` indices, and an
inverse-power order `M`.

Claim: the total weight equals the weighted finite Newton expansion at those nodes.

Proof: multiply the inverse-power interpolation identity by each weighted power and
exchange the finite sums.

Role: transfers reciprocal-power interpolation to the later power-sum block.
-/
theorem total_weight_eq_newton_evaluations (z : ℕ → ℂˣ) (a : ℕ → ℂ) (n M : ℕ) :
    (∑ j ∈ Finset.range n, a j) =
      ∑ k ∈ Finset.range n,
        reciprocalProductCoefficient z k M *
          (∑ j ∈ Finset.range n,
            a j * (z j : ℂ) ^ (M + 1) * (newtonRootPolynomial z k).eval (z j : ℂ)) := by
  calc
    _ = ∑ j ∈ Finset.range n, (a j * (z j : ℂ) ^ (M + 1)) * ((z j : ℂ) ^ (M + 1))⁻¹ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), mul_one]
    _ =
        ∑ j ∈ Finset.range n,
          ∑ k ∈ Finset.range n,
            reciprocalProductCoefficient z k M *
              (a j * (z j : ℂ) ^ (M + 1) * (newtonRootPolynomial z k).eval (z j : ℂ)) :=
      by
      apply Finset.sum_congr rfl
      intro j hj
      have h :
        ((z j : ℂ) ^ (M + 1))⁻¹ =
          ∑ k ∈ Finset.range n,
            (newtonRootPolynomial z k).eval (z j : ℂ) * reciprocalProductCoefficient z k M := by
        simpa only [newtonRootPolynomial, reciprocalProductCoefficient, Polynomial.eval_prod,
          Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X] using
          inversePower_newton_interpolation z n M j (Finset.mem_range.mp hj)
      rw [h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]

/--
Inputs: a weighted family of `n` nonzero nodes, prefix norm bounds, and a common bound `B` for
the power-sum exponents from `M + 1` through `M + k + 1`.

Claim: the norm of the `k`th weighted Newton term is at most
`choose (k + M) k * 2 ^ k * B`.

Proof: expand the root polynomial, bound each coefficient, and sum the binomial row.

Role: supplies the individual terms of the quantitative Turán estimate.
-/
theorem newton_evaluation_norm_le (z : ℕ → ℂˣ) (a : ℕ → ℂ) (n M k : ℕ)
    (hz : ∀ i < k + 1, (1 : ℝ) ≤ ‖(z i : ℂ)‖) (B : ℝ)
    (hB : ∀ l < k + 1, ‖∑ j ∈ Finset.range n, a j * (z j : ℂ) ^ (M + 1 + l)‖ ≤ B) :
    ‖reciprocalProductCoefficient z k M *
          (∑ j ∈ Finset.range n,
            a j * (z j : ℂ) ^ (M + 1) * (newtonRootPolynomial z k).eval (z j : ℂ))‖ ≤
      (Nat.choose (k + M) k : ℝ) * 2 ^ k * B := by
  rw [weighted_polynomial_eval_eq_power_sum (Finset.range n) (fun j ↦ (z j : ℂ)) a
      (newtonRootPolynomial z k) (newtonRootPolynomial_natDegree_lt z k) (M + 1),
    Finset.mul_sum]
  apply le_trans (norm_sum_le _ _)
  calc
    _ ≤ ∑ l ∈ Finset.range (k + 1), (Nat.choose (k + M) k : ℝ) * (Nat.choose k l : ℝ) * B := by
      apply Finset.sum_le_sum
      intro l hl
      rw [← mul_assoc, norm_mul]
      exact
        mul_le_mul
          (newton_term_coeff_norm_le_choose z k M l (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) hz)
          (hB l (Finset.mem_range.mp hl)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      have h : (∑ l ∈ Finset.range (k + 1), (Nat.choose k l : ℝ)) = 2 ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [h]

/--
Inputs: `n` nonzero complex nodes of norm at least one, complex weights, an initial exponent,
and a common norm bound for the following block of `n` power sums.

Claim: the total weight has norm at most the common bound times the finite Turán factor
`∑ k < n, choose (k + M) k * 2 ^ k`.

Proof: sum the individual Newton-term bounds in the total-weight identity.

Role: provides the quantitative block estimate for arbitrary initial exponents and repeated nodes.
-/
theorem total_weight_norm_le_turan_factor (z : ℕ → ℂˣ) (a : ℕ → ℂ) (n M : ℕ)
    (hz : ∀ i < n, (1 : ℝ) ≤ ‖(z i : ℂ)‖) (B : ℝ)
    (hB : ∀ l < n, ‖∑ j ∈ Finset.range n, a j * (z j : ℂ) ^ (M + 1 + l)‖ ≤ B) :
    ‖∑ j ∈ Finset.range n, a j‖ ≤
      (∑ k ∈ Finset.range n, (Nat.choose (k + M) k : ℝ) * 2 ^ k) * B := by
  rw [total_weight_eq_newton_evaluations z a n M]
  apply le_trans (norm_sum_le _ _)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  exact
    newton_evaluation_norm_le z a n M k
      (fun i hi ↦ hz i (Nat.lt_of_lt_of_le hi (Finset.mem_range.mp hk))) B
      (fun l hl ↦ hB l (Nat.lt_of_lt_of_le hl (Finset.mem_range.mp hk)))

/--
Inputs: a positive block length and an initial exponent.

Claim: the finite Turán factor is positive.

Proof: its terms are nonnegative and the term at zero equals one.

Role: permits division by the factor in the quantitative witness theorem.
-/
theorem turan_factor_pos (n M : ℕ) (hn : 0 < n) :
    0 < ∑ k ∈ Finset.range n, (Nat.choose (k + M) k : ℝ) * 2 ^ k := by
  apply Finset.sum_pos'
  · intro k hk
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _)
  · refine ⟨0, Finset.mem_range.mpr hn, ?_⟩
    simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, zero_lt_one]

/--
Inputs: a positive number of nonzero complex nodes of norm at least one, arbitrary weights,
and an initial exponent `M`.

Claim: some exponent in `M + 1, …, M + n` has weighted power-sum norm at least the total-weight
norm divided by `∑ k < n, choose (k + M) k * 2 ^ k`. Nodes may repeat.

Proof: choose the largest norm in the block and apply the finite Newton estimate.

Role: is the quantitative Turán first-main-theorem form needed for zero detection.
-/
theorem exists_power_sum_norm_ge_turan (z : ℕ → ℂˣ) (a : ℕ → ℂ) (n M : ℕ) (hn : 0 < n)
    (hz : ∀ i < n, (1 : ℝ) ≤ ‖(z i : ℂ)‖) :
    ∃ l ∈ Finset.range n,
      ‖∑ j ∈ Finset.range n, a j‖ / (∑ k ∈ Finset.range n, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
        ‖∑ j ∈ Finset.range n, a j * (z j : ℂ) ^ (M + 1 + l)‖ := by
  obtain ⟨l, hl, hmax⟩ :=
    (Finset.range n).exists_max_image
      (fun r ↦ ‖∑ j ∈ Finset.range n, a j * (z j : ℂ) ^ (M + 1 + r)‖)
      (Finset.nonempty_range_iff.mpr (ne_of_gt hn))
  refine ⟨l, hl, (div_le_iff₀ (turan_factor_pos n M hn)).mpr ?_⟩
  rw [mul_comm]
  exact total_weight_norm_le_turan_factor z a n M hz _ (fun r hr ↦ hmax r (Finset.mem_range.mpr hr))

/--
Inputs: a positive block length, arbitrary complex frequencies of norm at least one on the
selected indices, and arbitrary complex weights.

Claim: some weighted power sum in the block beginning at `M + 1` satisfies the Turán lower bound.
Only selected frequencies must be nonzero; repeated frequencies are allowed.

Proof: represent the selected frequencies as units and apply the unit-valued theorem.

Role: exposes the quantitative power-sum theorem without a unit-valued input requirement.
-/
theorem exists_weighted_power_sum_norm_ge_turan (z a : ℕ → ℂ) (n M : ℕ) (hn : 0 < n)
    (hz : ∀ i < n, (1 : ℝ) ≤ ‖z i‖) :
    ∃ l ∈ Finset.range n,
      ‖∑ j ∈ Finset.range n, a j‖ / (∑ k ∈ Finset.range n, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
        ‖∑ j ∈ Finset.range n, a j * z j ^ (M + 1 + l)‖ := by
  let u : ℕ → ℂˣ := fun i ↦
    if hi : i < n then Units.mk0 (z i) (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (hz i hi)))
    else 1
  have hu : ∀ i < n, (u i : ℂ) = z i := by
    intro i hi
    simp only [u, dite_eq_left hi, Units.val_mk0]
  obtain ⟨l, hl, hle⟩ :=
    exists_power_sum_norm_ge_turan u a n M hn (fun i hi ↦ (hu i hi).symm ▸ hz i hi)
  refine ⟨l, hl, ?_⟩
  have heq :
    (∑ j ∈ Finset.range n, a j * (u j : ℂ) ^ (M + 1 + l)) =
      ∑ j ∈ Finset.range n, a j * z j ^ (M + 1 + l) :=
    Finset.sum_congr rfl (fun j hj ↦ by rw [hu j (Finset.mem_range.mp hj)])
  rw [heq] at hle
  exact hle

/--
入力/前提: 有限集合上の複素周波数と重み、正の要素数、各周波数のノルム下界。
主張: 集合上の重み付き冪和のうち、連続する要素数分の指数のいずれかがTurán下界を満たす。
内容: 有限集合を `Fin s.card` で添字付け、自然数列上の重み付きTurán評価へ移す。
役割: 有限個の局所零点を重複度付き周波数として零点検出へ渡す。
-/
theorem exists_finset_weighted_power_sum_norm_ge_turan {α : Type} (s : Finset α) (a z : α → ℂ)
    (M : ℕ) (hs : 0 < s.card) (hz : ∀ u ∈ s, (1 : ℝ) ≤ ‖z u‖) :
    ∃ l ∈ Finset.range s.card,
      ‖∑ u ∈ s, a u‖ / (∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
        ‖∑ u ∈ s, a u * z u ^ (M + 1 + l)‖ := by
  classical
  let e := s.equivFin
  let az : ℕ → ℂ := fun i => if hi : i < s.card then a (e.symm ⟨i, hi⟩).val else 0
  let zz : ℕ → ℂ := fun i => if hi : i < s.card then z (e.symm ⟨i, hi⟩).val else 1
  have hzz : ∀ i < s.card, (1 : ℝ) ≤ ‖zz i‖ := by
    intro i hi
    simp only [zz, dite_eq_left hi]
    exact hz _ (e.symm ⟨i, hi⟩).property
  obtain ⟨l, hl, hT⟩ := exists_weighted_power_sum_norm_ge_turan zz az s.card M hs hzz
  have hsum (f : α → ℂ) :
    (∑ i ∈ Finset.range s.card, if hi : i < s.card then f (e.symm ⟨i, hi⟩).val else 0) =
      ∑ u ∈ s, f u := by
    calc
      _ = ∑ i : Fin s.card, f (e.symm i).val := by
        symm
        rw [Finset.sum_fin_eq_sum_range]
      _ = ∑ u ∈ s, f u := by
        calc
          _ = ∑ u : s, f u.val := Equiv.sum_comp e.symm (fun u : s => f u.val)
          _ = _ := Finset.sum_coe_sort s f
  have hbase : (∑ i ∈ Finset.range s.card, az i) = ∑ u ∈ s, a u := by
    calc
      _ = ∑ i ∈ Finset.range s.card, if hi : i < s.card then a (e.symm ⟨i, hi⟩).val else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [az, dite_eq_left (Finset.mem_range.mp hi)]
      _ = _ := hsum a
  have hpower (p : ℕ) : (∑ i ∈ Finset.range s.card, az i * zz i ^ p) = ∑ u ∈ s, a u * z u ^ p := by
    calc
      _ =
          ∑ i ∈ Finset.range s.card,
            (if hi : i < s.card then a (e.symm ⟨i, hi⟩).val * z (e.symm ⟨i, hi⟩).val ^ p else 0) :=
        by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [az, zz, dite_eq_left (Finset.mem_range.mp hi)]
      _ = _ := hsum (fun u => a u * z u ^ p)
  refine ⟨l, hl, ?_⟩
  rw [← hbase, ← hpower (M + 1 + l)]
  exact hT

/--
Inputs: a positive number of complex frequencies of norm at least one and an initial exponent.

Claim: one of the next `n` pure power sums has norm at least `n` divided by the finite Turán
factor. Repetitions are allowed and contribute separately.

Proof: set all weights equal to one in the weighted theorem.

Role: gives the multiplicity-sensitive finite power-sum estimate used by zero detectors.
-/
theorem exists_pure_power_sum_norm_ge_turan (z : ℕ → ℂ) (n M : ℕ) (hn : 0 < n)
    (hz : ∀ i < n, (1 : ℝ) ≤ ‖z i‖) :
    ∃ l ∈ Finset.range n,
      (n : ℝ) / (∑ k ∈ Finset.range n, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤
        ‖∑ j ∈ Finset.range n, z j ^ (M + 1 + l)‖ := by
  simpa only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Complex.norm_natCast] using exists_weighted_power_sum_norm_ge_turan z (fun _ ↦ 1) n M hn hz

private theorem turan_term_nat_le_two_pow (n M : ℕ) :
    Nat.choose (n + M) n * 2 ^ n ≤ 2 ^ (M + 2 * n) := by
  calc
    _ ≤ 2 ^ (n + M) * 2 ^ n := Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = _ := by
      rw [← pow_add]; congr 1; ring

private theorem turan_factor_nat_le_two_pow (n M : ℕ) :
    (∑ k ∈ Finset.range n, Nat.choose (k + M) k * 2 ^ k) ≤ 2 ^ (M + 2 * n) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]; exact Nat.zero_le _
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ ≤ 2 ^ (M + 2 * n) + 2 ^ (M + 2 * n) := Nat.add_le_add ih (turan_term_nat_le_two_pow n M)
      _ = 2 * 2 ^ (M + 2 * n) := (two_mul _).symm
      _ ≤ 4 * 2 ^ (M + 2 * n) := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by
        rw [show M + 2 * (n + 1) = M + 2 * n + 2 by ring, pow_add]
        ring

/--
Inputs: a block length and an initial exponent.

Claim: the finite Turán factor is at most `2 ^ (M + 2 * n)`.

Proof: bound each binomial coefficient by a power of two and induct on the block length.

Role: gives a coarse exponential estimate without an additional logarithmic factor.
-/
theorem turan_factor_le_two_pow (n M : ℕ) :
    (∑ k ∈ Finset.range n, (Nat.choose (k + M) k : ℝ) * 2 ^ k) ≤ 2 ^ (M + 2 * n) := by
  exact_mod_cast turan_factor_nat_le_two_pow n M

/--
Inputs: a positive number of complex frequencies of norm at least one and an initial exponent.

Claim: a pure power sum in the following block has norm at least `n / 2 ^ (M + 2 * n)`.
Repeated frequencies are counted separately.

Proof: weaken the exact finite Turán denominator to its exponential upper bound.

Role: provides an explicit exponential lower bound for finite zero detectors.
-/
theorem exists_pure_power_sum_norm_ge_two_pow (z : ℕ → ℂ) (n M : ℕ) (hn : 0 < n)
    (hz : ∀ i < n, (1 : ℝ) ≤ ‖z i‖) :
    ∃ l ∈ Finset.range n,
      (n : ℝ) / 2 ^ (M + 2 * n) ≤ ‖∑ j ∈ Finset.range n, z j ^ (M + 1 + l)‖ := by
  obtain ⟨l, hl, hle⟩ := exists_pure_power_sum_norm_ge_turan z n M hn hz
  exact
    ⟨l, hl,
      le_trans
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (turan_factor_pos n M hn)
          (turan_factor_le_two_pow n M))
        hle⟩

/--
Inputs: a positive-length list of complex points in a disk of positive radius `R` about `s`,
none equal to `s`, and an initial exponent `M`.

Claim: one reciprocal-distance power sum in the following block is bounded below by
`n / (2 ^ (M + 2 * n) * R ^ (M + 1 + l))`. Repeated points contribute separately.

Proof: normalize inverse distances by the radius and apply the exponential Turán bound.

Role: connects the finite power-sum theorem to local lists of zeros with multiplicities.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_disk (ρ : ℕ → ℂ) (s : ℂ) (n M : ℕ) (hn : 0 < n)
    (R : ℝ) (hR : 0 < R) (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ R) :
    ∃ l ∈ Finset.range n,
      (n : ℝ) / (2 ^ (M + 2 * n) * R ^ (M + 1 + l)) ≤
        ‖∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)‖ := by
  have hRnorm : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let z : ℕ → ℂ := fun j ↦ (R : ℂ) * (s - ρ j)⁻¹
  have hz : ∀ j < n, (1 : ℝ) ≤ ‖z j‖ := by
    intro j hj
    rw [show z j = (R : ℂ) * (s - ρ j)⁻¹ from rfl, norm_mul, hRnorm, norm_inv, ← div_eq_mul_inv]
    exact (one_le_div (hρ j hj).1).mpr (hρ j hj).2
  obtain ⟨l, hl, hle⟩ := exists_pure_power_sum_norm_ge_two_pow z n M hn hz
  have heq :
    ‖∑ j ∈ Finset.range n, z j ^ (M + 1 + l)‖ =
      R ^ (M + 1 + l) * ‖∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)‖ := by
    simp only [z, mul_pow, ← Finset.mul_sum, norm_mul, norm_pow, hRnorm]
  rw [heq] at hle
  refine ⟨l, hl, ?_⟩
  rw [← div_div, div_le_iff₀ (pow_pos hR _)]
  simpa only [mul_comm] using hle

/-!
## Finite weighted reciprocal sums
-/

/--
Inputs: a nonempty finite family of complex zeros, complex weights, a center, and a positive
radius containing every zero while excluding the center.
Claim: one of the next `s.card` weighted reciprocal-distance power sums has an explicit lower bound
in terms of the norm of the total weight.
Proof: normalize every reciprocal distance by `R`, apply the finite weighted Turán estimate, and
bound its denominator by `2^(M + 2*s.card)`.
Role: carries multiplicities as weights when a finite local zero family is used for detection.
-/
theorem exists_finset_weighted_reciprocal_power_sum_norm_ge_of_disk (s : Finset ℂ) (center : ℂ)
    (a : ℂ → ℂ) (M : ℕ) (hs : 0 < s.card) (R : ℝ) (hR : 0 < R)
    (hzeros : ∀ ρ ∈ s, 0 < ‖center - ρ‖ ∧ ‖center - ρ‖ ≤ R) :
    ∃ l ∈ Finset.range s.card,
      ‖∑ ρ ∈ s, a ρ‖ / (2 ^ (M + 2 * s.card) * R ^ (M + 1 + l)) ≤
        ‖∑ ρ ∈ s, a ρ * ((center - ρ)⁻¹) ^ (M + 1 + l)‖ := by
  have hRnorm : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let z : ℂ → ℂ := fun ρ ↦ (R : ℂ) * (center - ρ)⁻¹
  have hz : ∀ ρ ∈ s, (1 : ℝ) ≤ ‖z ρ‖ := by
    intro ρ hρ
    rw [show z ρ = (R : ℂ) * (center - ρ)⁻¹ from rfl, norm_mul, hRnorm, norm_inv, ← div_eq_mul_inv]
    exact (one_le_div (hzeros ρ hρ).1).mpr (hzeros ρ hρ).2
  obtain ⟨l, hl, hTuran⟩ := exists_finset_weighted_power_sum_norm_ge_turan s a z M hs hz
  have hfactor :
    ∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k ≤ 2 ^ (M + 2 * s.card) :=
    turan_factor_le_two_pow s.card M
  have hden : 0 < ∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k :=
    turan_factor_pos s.card M hs
  have hbase : ‖∑ ρ ∈ s, a ρ‖ / 2 ^ (M + 2 * s.card) ≤ ‖∑ ρ ∈ s, a ρ * z ρ ^ (M + 1 + l)‖ := by
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hden hfactor).trans hTuran
  have heq :
    ‖∑ ρ ∈ s, a ρ * z ρ ^ (M + 1 + l)‖ =
      R ^ (M + 1 + l) * ‖∑ ρ ∈ s, a ρ * ((center - ρ)⁻¹) ^ (M + 1 + l)‖ := by
    have hsum :
      (∑ ρ ∈ s, a ρ * z ρ ^ (M + 1 + l)) =
        (R : ℂ) ^ (M + 1 + l) * ∑ ρ ∈ s, a ρ * ((center - ρ)⁻¹) ^ (M + 1 + l) := by
      calc
        _ = ∑ ρ ∈ s, (R : ℂ) ^ (M + 1 + l) * (a ρ * ((center - ρ)⁻¹) ^ (M + 1 + l)) := by
          apply Finset.sum_congr rfl
          intro ρ hρ
          simp only [z, mul_pow]
          ring
        _ = _ := by rw [Finset.mul_sum]
    rw [hsum, norm_mul, norm_pow, hRnorm]
  rw [heq] at hbase
  refine ⟨l, hl, ?_⟩
  rw [← div_div, div_le_iff₀ (pow_pos hR _)]
  simpa only [mul_comm] using hbase

/--
Inputs: a nonempty finite family of complex zeros, a center, and a positive radius containing
every zero while excluding the center.
Claim: one of the next `s.card` reciprocal-distance power sums has norm at least
`s.card / (2^(M+2*s.card) * R^k)`.
Proof: normalize all reciprocal distances by `R`, apply the finite weighted Turán estimate, and
use the exponential upper bound for its denominator.
Role: gives a multiplicity-preserving local power-sum lower bound directly on a finite zero set.
-/
theorem exists_finset_reciprocal_power_sum_norm_ge_of_disk (s : Finset ℂ) (center : ℂ) (M : ℕ)
    (hs : 0 < s.card) (R : ℝ) (hR : 0 < R) (hzeros : ∀ ρ ∈ s, 0 < ‖center - ρ‖ ∧ ‖center - ρ‖ ≤ R) :
    ∃ l ∈ Finset.range s.card,
      (s.card : ℝ) / (2 ^ (M + 2 * s.card) * R ^ (M + 1 + l)) ≤
        ‖∑ ρ ∈ s, ((center - ρ)⁻¹) ^ (M + 1 + l)‖ := by
  have hRnorm : ‖(R : ℂ)‖ = R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  let z : ℂ → ℂ := fun ρ ↦ (R : ℂ) * (center - ρ)⁻¹
  have hz : ∀ ρ ∈ s, (1 : ℝ) ≤ ‖z ρ‖ := by
    intro ρ hρ
    rw [show z ρ = (R : ℂ) * (center - ρ)⁻¹ from rfl, norm_mul, hRnorm, norm_inv, ← div_eq_mul_inv]
    exact (one_le_div (hzeros ρ hρ).1).mpr (hzeros ρ hρ).2
  obtain ⟨l, hl, hTuran⟩ := exists_finset_weighted_power_sum_norm_ge_turan s (fun _ ↦ 1) z M hs hz
  have hfactor :
    ∑ k ∈ Finset.range s.card, (Nat.choose (k + M) k : ℝ) * 2 ^ k ≤ 2 ^ (M + 2 * s.card) :=
    turan_factor_le_two_pow s.card M
  have hbase : (s.card : ℝ) / 2 ^ (M + 2 * s.card) ≤ ‖∑ ρ ∈ s, z ρ ^ (M + 1 + l)‖ := by
    have hden := turan_factor_pos s.card M hs
    have hnumerator : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    have hratio := div_le_div_of_nonneg_left hnumerator hden hfactor
    have hrewrite : ‖∑ ρ ∈ s, (fun _ : ℂ => (1 : ℂ)) ρ‖ = (s.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast]
    have hTuran' := hTuran
    rw [hrewrite] at hTuran'
    exact hratio.trans (by simpa only [one_mul] using hTuran')
  have heq :
    ‖∑ ρ ∈ s, z ρ ^ (M + 1 + l)‖ = R ^ (M + 1 + l) * ‖∑ ρ ∈ s, ((center - ρ)⁻¹) ^ (M + 1 + l)‖ := by
    simp only [z, mul_pow, ← Finset.mul_sum, norm_mul, norm_pow, hRnorm]
  rw [heq] at hbase
  refine ⟨l, hl, ?_⟩
  rw [← div_div, div_le_iff₀ (pow_pos hR _)]
  simpa only [mul_comm] using hbase

/--
Inputs: a finite list of distinct-or-repeated zeros at positive distance from a center, all within
radius `3η`, and a positive width `η`.
Claim: one of the next `n` reciprocal-distance power sums has an explicit positive lower bound.
Proof: apply the existing reciprocal power-sum estimate to the disk of radius `3η`.
Role: estimates a local sum of zeros satisfying `1-η ≤ Re ρ ≤ 1` and `|t-Im ρ| ≤ η`.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk (ρ : ℕ → ℂ) (s : ℂ) (n M : ℕ)
    (hn : 0 < n) {η : ℝ} (hη : 0 < η) (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) :
    ∃ l ∈ Finset.range n,
      (n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l)) ≤
        ‖∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)‖ := by
  exact exists_reciprocal_power_sum_norm_ge_of_disk ρ s n M hn (3 * η) (by positivity) hρ

/--
Inputs: a finite set of complex numbers, a power, and a uniform upper bound for their norms.
Claim: the norm of their power sum is at most the number of terms times the same power of the
norm bound.
Proof: apply the triangle inequality termwise, then use monotonicity of natural powers.
Role: bounds the contribution of zeros outside a selected local disk.
-/
theorem norm_sum_powers_le_card_mul_pow_of_norm_le {ι : Type} (s : Finset ι) (z : ι → ℂ) (k : ℕ)
    {r : ℝ} (hz : ∀ i ∈ s, ‖z i‖ ≤ r) : ‖∑ i ∈ s, z i ^ k‖ ≤ (s.card : ℝ) * r ^ k := by
  calc
    ‖∑ i ∈ s, z i ^ k‖ ≤ ∑ i ∈ s, ‖z i ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, r ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hz i hi) k
    _ = (s.card : ℝ) * r ^ k := by simp only [Finset.sum_const, nsmul_eq_mul]

/--
Inputs: a nonempty list of zeros within distance `3η` of a center, a finite list outside the
local disk, and an upper bound for the inverse distances of the outside list.
Claim: one exponent has a lower bound for the combined reciprocal power sum equal to the local
Turán lower bound minus the largest possible outside contribution.
Proof: apply the local-disk Turán estimate, bound the outside sum termwise, and use the reverse
triangle inequality.
Role: separates the local zero contribution from the tail before proving that the error is small.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_tail (ρ τ : ℕ → ℂ) (s : ℂ)
    (n m M : ℕ) (hn : 0 < n) {η : ℝ} (hη : 0 < η) (Rtail : ℝ)
    (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) (hτ : ∀ j < m, ‖(s - τ j)⁻¹‖ ≤ Rtail) :
    ∃ l ∈ Finset.range n,
      (n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l)) - (m : ℝ) * Rtail ^ (M + 1 + l) ≤
        ‖(∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)) +
            ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l)‖ := by
  obtain ⟨l, hl, hlocal⟩ := exists_reciprocal_power_sum_norm_ge_of_three_eta_disk ρ s n M hn hη hρ
  have htail :=
    norm_sum_powers_le_card_mul_pow_of_norm_le (Finset.range m) (fun j => (s - τ j)⁻¹) (M + 1 + l)
      (by
        intro j hj
        exact hτ j (Finset.mem_range.mp hj))
  have htail' :
    ‖∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l)‖ ≤ (m : ℝ) * Rtail ^ (M + 1 + l) := by
    simpa only [Finset.card_range] using htail
  have htriangle :=
    norm_sub_le
      ((∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)) +
        ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l))
      (∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l))
  rw [add_sub_cancel_right] at htriangle
  refine ⟨l, hl, ?_⟩
  linarith only [hlocal, htail', htriangle]

/--
Inputs: a local scale `η`, a tail radius, and a base-exponent tail margin.
Claim: the base margin controls every later exponent when the scaled tail radius is at most one.
Proof: compare the powers by antitonicity on `[0, 1]`, then clear the positive denominator.
Role: derives the uniform margin needed to absorb a geometric tail into a local Turán bound.
-/
theorem tail_power_margin_of_ratio (n m M l : ℕ) {η Rtail : ℝ} (hη : 0 < η) (hRtail : 0 ≤ Rtail)
    (hscale : 3 * η * Rtail ≤ 1)
    (hbase : 2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1) ≤ (n : ℝ) / 2 ^ (M + 2 * n)) :
    2 * ((m : ℝ) * Rtail ^ (M + 1 + l)) ≤ (n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l)) := by
  have hb0 : 0 ≤ 3 * η * Rtail := by positivity
  have hp := pow_le_pow_of_le_one hb0 hscale (Nat.le_add_right (M + 1) l)
  have hpower : 2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1 + l) ≤ (n : ℝ) / 2 ^ (M + 2 * n) := by
    calc
      2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1 + l) ≤ 2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (n : ℝ) / 2 ^ (M + 2 * n) := hbase
  rw [le_div_iff₀ (by positivity)]
  calc
    (2 * ((m : ℝ) * Rtail ^ (M + 1 + l))) * (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l)) =
        (2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1 + l)) * 2 ^ (M + 2 * n) :=
      by
      rw [mul_pow]; ring
    _ ≤ ((n : ℝ) / 2 ^ (M + 2 * n)) * 2 ^ (M + 2 * n) :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = (n : ℝ) := by rw [div_mul_cancel₀ _ (by positivity)]

/--
Inputs: a positive local multiplicity count and a nonnegative tail ratio strictly below one half.
Claim: some starting exponent makes the first tail term at most the local Turán lower bound.
Proof: the geometric sequence with ratio twice the tail ratio tends to zero; choose an exponent
where it is smaller than the explicit threshold determined by the local count and block length.
Role: removes the free initial-margin premise from the geometric-tail zero detector.
-/
theorem exists_exponent_tail_base_margin_of_ratio_lt_half (m n : ℕ) (hn : 0 < n) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1 / 2) :
    ∃ M : ℕ, 2 * (m : ℝ) * r ^ (M + 1) ≤ (n : ℝ) / 2 ^ (M + 2 * n) := by
  let A : ℝ := 2 * (m : ℝ) * r + 1
  let B : ℝ := 2 ^ (2 * n)
  have hlim : Filter.Tendsto (fun M : ℕ => (2 * r) ^ M) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by linarith only [hr])
  have hε : 0 < (n : ℝ) / (A * B) := by
    dsimp [A, B]
    positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ((n : ℝ) / (A * B)) hε
  refine ⟨N, ?_⟩
  have hdist := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hdist
  have hp : 0 ≤ (2 * r) ^ N := by positivity
  rw [abs_of_nonneg hp] at hdist
  have hABpos : 0 < A * B := by positivity
  have hprod : (2 * r) ^ N * (A * B) < n := (lt_div_iff₀ hABpos).mp hdist
  have hfactor :
    2 * (m : ℝ) * r ^ (N + 1) * 2 ^ (N + 2 * n) =
      (2 * (m : ℝ) * r) * (2 * r) ^ N * 2 ^ (2 * n) := by
    rw [pow_add]
    ring
  have hcoef : 2 * (m : ℝ) * r ≤ A := by
    dsimp [A]
    linarith only [mul_nonneg (Nat.cast_nonneg m) hr0]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (N + 2 * n))]
  rw [hfactor]
  calc
    (2 * (m : ℝ) * r) * (2 * r) ^ N * 2 ^ (2 * n) =
        (2 * (m : ℝ) * r) * ((2 * r) ^ N * 2 ^ (2 * n)) :=
      by ring
    _ ≤ A * ((2 * r) ^ N * 2 ^ (2 * n)) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (2 * r) ^ N * (A * B) := by
      dsimp [B]; ring
    _ ≤ n := le_of_lt hprod

/--
Inputs: the number of remote terms and a positive local block length.
Claim: for remote-to-near ratio `3/8`, the initial tail margin holds at the explicit exponent
`4 * (m + 2 * n)`.
Proof: use `(3/4)^4 ≤ 1/2`, cancel the height-block factor, and bound `m / 2^m` by one.
Role: makes the starting exponent in the separated-zero detector linear in the local and remote
term counts.
-/
theorem tail_base_margin_of_ratio_three_eighths (m n : ℕ) (hn : 0 < n) :
    2 * (m : ℝ) * (3 / 8 : ℝ) ^ (4 * (m + 2 * n) + 1) ≤
      (n : ℝ) / 2 ^ (4 * (m + 2 * n) + 2 * n) := by
  let a : ℕ := m + 2 * n
  have hstep : (3 / 4 : ℝ) ^ 4 ≤ 1 / 2 := by norm_num only
  have hgeom : (3 / 4 : ℝ) ^ (4 * a) ≤ (1 / 2 : ℝ) ^ a := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num only) hstep _
  have hcancel : (1 / 2 : ℝ) ^ (2 * n) * 2 ^ (2 * n) = 1 := by
    rw [← mul_pow]
    norm_num only [one_pow]
  have hgeom' : (3 / 4 : ℝ) ^ (4 * (m + 2 * n)) * 2 ^ (2 * n) ≤ (1 / 2 : ℝ) ^ m := by
    have hgeom'' : (3 / 4 : ℝ) ^ (4 * (m + 2 * n)) ≤ (1 / 2 : ℝ) ^ (m + 2 * n) := by
      change (3 / 4 : ℝ) ^ (4 * a) ≤ (1 / 2 : ℝ) ^ a
      exact hgeom
    calc
      _ ≤ (1 / 2 : ℝ) ^ (m + 2 * n) * 2 ^ (2 * n) :=
        mul_le_mul_of_nonneg_right hgeom'' (by positivity)
      _ = (1 / 2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ (2 * n) * 2 ^ (2 * n)) := by
        rw [pow_add]; ring
      _ = _ := by rw [hcancel, mul_one]
  let M : ℕ := 4 * (m + 2 * n)
  have hpowid : (3 / 8 : ℝ) ^ (M + 1) * 2 ^ M = (3 / 8 : ℝ) * (3 / 4 : ℝ) ^ M := by
    rw [pow_succ]
    calc
      ((3 / 8 : ℝ) ^ M * (3 / 8 : ℝ)) * 2 ^ M = ((3 / 8 : ℝ) ^ M * 2 ^ M) * (3 / 8 : ℝ) := by ring
      _ = ((3 / 8 : ℝ) * 2) ^ M * (3 / 8 : ℝ) := by rw [← mul_pow]
      _ = (3 / 4 : ℝ) ^ M * (3 / 8 : ℝ) := by norm_num only
      _ = _ := by ring
  have hdenpow : (2 : ℝ) ^ (M + 2 * n) = 2 ^ M * 2 ^ (2 * n) := by rw [pow_add]
  have hprod : (2 * (m : ℝ) * (3 / 8 : ℝ) ^ (M + 1)) * 2 ^ (M + 2 * n) ≤ n := by
    rw [hdenpow]
    calc
      2 * (m : ℝ) * (3 / 8 : ℝ) ^ (M + 1) * (2 ^ M * 2 ^ (2 * n)) =
          2 * (m : ℝ) * ((3 / 8 : ℝ) ^ (M + 1) * 2 ^ M) * 2 ^ (2 * n) :=
        by ring
      _ = 2 * (m : ℝ) * ((3 / 8 : ℝ) * (3 / 4 : ℝ) ^ M) * 2 ^ (2 * n) := by rw [hpowid]
      _ = (3 / 4 : ℝ) * (m : ℝ) * ((3 / 4 : ℝ) ^ (4 * (m + 2 * n)) * 2 ^ (2 * n)) := by
        dsimp only [M]
        ring
      _ ≤ (3 / 4 : ℝ) * (m : ℝ) * (1 / 2 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_left hgeom' (by positivity)
      _ ≤ (m : ℝ) * (1 / 2 : ℝ) ^ m := by
        have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
        have hmul : (3 / 4 : ℝ) * (m : ℝ) ≤ (m : ℝ) := by nlinarith only [hmnonneg]
        exact mul_le_mul_of_nonneg_right hmul (pow_nonneg (by norm_num only) _)
      _ ≤ 1 := by
        have hnat : 2 * m ≤ 2 ^ m := Nat.mul_le_pow (by decide) m
        have hmle : m ≤ 2 ^ m := by omega
        have hpow : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
          rw [← mul_pow]
          norm_num only [one_pow]
        calc
          (m : ℝ) * (1 / 2 : ℝ) ^ m ≤ (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hmle) (pow_nonneg (by norm_num only) _)
          _ = 1 := hpow
      _ ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
  have hdiv := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (M + 2 * n))).2 hprod
  simpa only [M] using hdiv

/--
Inputs: the local and tail data from the preceding split estimate,
with a uniform inequality making the tail at most half the local lower bound on the exponent block.
Claim: one combined reciprocal power sum is at least half the local Turán lower bound.
Proof: apply the split estimate and the supplied arithmetic margin at its selected exponent.
Role: turns a quantitative tail estimate into a positive lower bound for zero detection.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_small_tail (ρ τ : ℕ → ℂ) (s : ℂ)
    (n m M : ℕ) (hn : 0 < n) {η : ℝ} (hη : 0 < η) (Rtail : ℝ)
    (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) (hτ : ∀ j < m, ‖(s - τ j)⁻¹‖ ≤ Rtail)
    (hmargin :
      ∀ l ∈ Finset.range n,
        2 * ((m : ℝ) * Rtail ^ (M + 1 + l)) ≤ (n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l))) :
    ∃ l ∈ Finset.range n,
      ((n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l))) / 2 ≤
        ‖(∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)) +
            ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l)‖ := by
  obtain ⟨l, hl, hsum⟩ :=
    exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_tail ρ τ s n m M hn hη Rtail hρ hτ
  refine ⟨l, hl, ?_⟩
  have hm := hmargin l hl
  linarith only [hsum, hm]

/--
Inputs: local zeros and a finite tail whose scaled radius and first exponent satisfy a ratio bound.
Claim: some exponent in the local Turán block gives at least half the local lower bound after
adding the tail.
Proof: derive the block-wide margin from `tail_power_margin_of_ratio` and apply the split estimate.
Role: provides a positive local power-sum bound without an unproved uniform-margin premise.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_geometric_tail (ρ τ : ℕ → ℂ)
    (s : ℂ) (n m M : ℕ) (hn : 0 < n) {η : ℝ} (hη : 0 < η) (Rtail : ℝ) (hRtail : 0 ≤ Rtail)
    (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) (hτ : ∀ j < m, ‖(s - τ j)⁻¹‖ ≤ Rtail)
    (hscale : 3 * η * Rtail ≤ 1)
    (hbase : 2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1) ≤ (n : ℝ) / 2 ^ (M + 2 * n)) :
    ∃ l ∈ Finset.range n,
      ((n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l))) / 2 ≤
        ‖(∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)) +
            ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l)‖ := by
  apply
    exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_small_tail ρ τ s n m M hn hη Rtail hρ
      hτ
  intro l hl
  exact tail_power_margin_of_ratio n m M l hη hRtail hscale hbase

/--
Inputs: local zeros within `3η`, a finite remote-zero tail, and a nonnegative tail radius whose
scaled ratio is strictly below one half.
Claim: some starting exponent and a subsequent block exponent give a positive combined reciprocal
power-sum lower bound, with no separately supplied first-exponent margin.
Proof: choose the starting exponent by geometric decay, then apply the uniform tail-margin theorem.
Role: exposes the tail-split detector at the point where the local and remote zero bounds meet.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_tail_ratio (ρ τ : ℕ → ℂ) (s : ℂ)
    (n m : ℕ) (hn : 0 < n) {η : ℝ} (hη : 0 < η) (Rtail : ℝ) (hRtail : 0 ≤ Rtail)
    (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) (hτ : ∀ j < m, ‖(s - τ j)⁻¹‖ ≤ Rtail)
    (hscale : 3 * η * Rtail < 1 / 2) :
    ∃ M : ℕ,
      ∃ l ∈ Finset.range n,
        ((n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l))) / 2 ≤
          ‖(∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)) +
              ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l)‖ := by
  have hratio0 : 0 ≤ 3 * η * Rtail := by positivity
  obtain ⟨M, hbase⟩ :=
    exists_exponent_tail_base_margin_of_ratio_lt_half m n hn hratio0 (by linarith only [hscale])
  obtain ⟨l, hl, hbound⟩ :=
    exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_geometric_tail ρ τ s n m M hn hη
      Rtail hRtail hρ hτ (le_of_lt (lt_trans hscale (by norm_num only : (1 / 2 : ℝ) < 1))) hbase
  exact ⟨M, l, hl, hbound⟩

/--
Inputs: local zeros within `3η` and a finite remote family whose points are at distance at least
`8η` from the center.
Claim: some starting exponent and a subsequent block exponent give a positive combined reciprocal
power-sum lower bound.
Proof: the remote inverse distances are at most `1/(8η)`, so their ratio to the local scale `3η`
is `3/8 < 1/2`; apply the automatic exponent-selection theorem.
Role: turns an annular zero separation into the finite-tail zero-detection interface.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_remote_distance (ρ τ : ℕ → ℂ)
    (s : ℂ) (n m : ℕ) (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) (hτ : ∀ j < m, 8 * η ≤ ‖s - τ j‖) :
    ∃ M : ℕ,
      ∃ l ∈ Finset.range n,
        ((n : ℝ) / (2 ^ (M + 2 * n) * (3 * η) ^ (M + 1 + l))) / 2 ≤
          ‖(∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (M + 1 + l)) +
              ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (M + 1 + l)‖ := by
  let Rtail : ℝ := (8 * η)⁻¹
  have hRtail : 0 ≤ Rtail := by
    dsimp [Rtail]; positivity
  have hτbound : ∀ j < m, ‖(s - τ j)⁻¹‖ ≤ Rtail := by
    intro j hj
    rw [norm_inv]
    dsimp [Rtail]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 * η) (hτ j hj)
  have hscale : 3 * η * Rtail < 1 / 2 := by
    dsimp [Rtail]
    have heq : 3 * η * (8 * η)⁻¹ = 3 / 8 := by field_simp [ne_of_gt hη]
    rw [heq]
    norm_num only
  exact
    exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_tail_ratio ρ τ s n m hn hη Rtail
      hRtail hρ hτbound hscale

/--
Inputs: local zeros in the `3η` disk and a finite remote family at distance at least `8η`.
Claim: the combined reciprocal power sum has the stated lower bound in a block starting at the
explicit exponent `4 * (m + 2 * n) + 1`.
Proof: specialize the geometric-tail detector at ratio `3/8` and use the explicit base margin.
Role: bounds the derivative-order range in terms of the near and remote zero counts.
-/
theorem exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_remote_distance_explicit
    (ρ τ : ℕ → ℂ) (s : ℂ) (n m : ℕ) (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hρ : ∀ j < n, 0 < ‖s - ρ j‖ ∧ ‖s - ρ j‖ ≤ 3 * η) (hτ : ∀ j < m, 8 * η ≤ ‖s - τ j‖) :
    ∃ l ∈ Finset.range n,
      ((n : ℝ) / (2 ^ (4 * (m + 2 * n) + 2 * n) * (3 * η) ^ (4 * (m + 2 * n) + 1 + l))) / 2 ≤
        ‖(∑ j ∈ Finset.range n, ((s - ρ j)⁻¹) ^ (4 * (m + 2 * n) + 1 + l)) +
            ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ (4 * (m + 2 * n) + 1 + l)‖ := by
  let M : ℕ := 4 * (m + 2 * n)
  let Rtail : ℝ := (8 * η)⁻¹
  have hRtail : 0 ≤ Rtail := by
    dsimp only [Rtail]
    positivity
  have hτbound : ∀ j < m, ‖(s - τ j)⁻¹‖ ≤ Rtail := by
    intro j hj
    rw [norm_inv]
    dsimp only [Rtail]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 * η) (hτ j hj)
  have hscale : 3 * η * Rtail ≤ 1 := by
    dsimp only [Rtail]
    have heq : 3 * η * (8 * η)⁻¹ = (3 / 8 : ℝ) := by field_simp [ne_of_gt hη]
    rw [heq]
    norm_num only
  have hbase : 2 * (m : ℝ) * (3 * η * Rtail) ^ (M + 1) ≤ (n : ℝ) / 2 ^ (M + 2 * n) := by
    dsimp only [Rtail, M]
    have heq : 3 * η * (8 * η)⁻¹ = (3 / 8 : ℝ) := by field_simp [ne_of_gt hη]
    rw [heq]
    exact tail_base_margin_of_ratio_three_eighths m n hn
  obtain ⟨l, hl, hbound⟩ :=
    exists_reciprocal_power_sum_norm_ge_of_three_eta_disk_with_geometric_tail ρ τ s n m M hn hη
      Rtail hRtail hρ hτbound hscale hbase
  refine ⟨l, hl, ?_⟩
  simpa only [M] using hbound

/--
Inputs: a distinguished zero within `5η/4` of the center and a remote zero at distance at least
`8η`.
Claim: the remote reciprocal norm is at most `5/32` times the distinguished reciprocal norm.
Proof: invert the two distance bounds and compare the resulting rational factors.
Role: quantifies the separation available when a local disk is centered at `1 + η + it` and the
distinguished zero lies within `η/4` of `1 + it`.
-/
theorem remote_inv_norm_le_five_thirtysecond_mul_near_inv_norm (s ρ τ : ℂ) {η : ℝ} (hη : 0 < η)
    (hnear0 : 0 < ‖s - ρ‖) (hnear : ‖s - ρ‖ ≤ 5 * η / 4) (hremote : 8 * η ≤ ‖s - τ‖) :
    ‖(s - τ)⁻¹‖ ≤ (5 / 32 : ℝ) * ‖(s - ρ)⁻¹‖ := by
  rw [norm_inv, norm_inv]
  have hremote' : 1 / ‖s - τ‖ ≤ 1 / (8 * η) := one_div_le_one_div_of_le (by positivity) hremote
  have hnear' : 1 / (5 * η / 4) ≤ 1 / ‖s - ρ‖ := one_div_le_one_div_of_le (by positivity) hnear
  have hbound : 1 / ‖s - τ‖ ≤ (5 / 32 : ℝ) * (1 / ‖s - ρ‖) := by
    calc
      1 / ‖s - τ‖ ≤ 1 / (8 * η) := hremote'
      _ = (5 / 32 : ℝ) * (1 / (5 * η / 4)) := by
        field_simp; ring
      _ ≤ (5 / 32 : ℝ) * (1 / ‖s - ρ‖) := mul_le_mul_of_nonneg_left hnear' (by norm_num only)
  simpa only [one_div] using hbound

/--
Inputs: a distinguished zero within `5η/4` of the center and a finite family at distance at least
`8η`.
Claim: each reciprocal power sum over the remote family is bounded by its cardinality times the
`k`th power of `5/32` times the distinguished reciprocal norm.
Proof: apply the pointwise reciprocal separation and the finite power-sum norm bound.
Role: supplies the finite remote-error term for the maximal-node zero detector.
-/
theorem norm_sum_remote_reciprocal_powers_le_of_near_zero (s ρ : ℂ) (τ : ℕ → ℂ) (m k : ℕ) {η : ℝ}
    (hη : 0 < η) (hnear0 : 0 < ‖s - ρ‖) (hnear : ‖s - ρ‖ ≤ 5 * η / 4)
    (hremote : ∀ j < m, 8 * η ≤ ‖s - τ j‖) :
    ‖∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ k‖ ≤ (m : ℝ) * ((5 / 32 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k := by
  have hbound :=
    norm_sum_powers_le_card_mul_pow_of_norm_le (Finset.range m) (fun j => (s - τ j)⁻¹) k (r :=
      (5 / 32 : ℝ) * ‖(s - ρ)⁻¹‖)
      (by
        intro j hj
        exact
          remote_inv_norm_le_five_thirtysecond_mul_near_inv_norm s ρ (τ j) hη hnear0 hnear
            (hremote j (Finset.mem_range.mp hj)))
  simpa only [Finset.card_range] using hbound

/--
Inputs: a distinguished zero within `5η/4` of the center and a remote zero at distance at least
`80η`.
Claim: the remote reciprocal norm is at most `1/64` times the distinguished reciprocal norm.
Proof: invert the distance bounds and compare the resulting rational factors.
Role: provides enough separation for the maximum-node power-sum lower bound with base `1/50`.
-/
theorem remote_inv_norm_le_one_sixtyfourth_mul_near_inv_norm (s ρ τ : ℂ) {η : ℝ} (hη : 0 < η)
    (hnear0 : 0 < ‖s - ρ‖) (hnear : ‖s - ρ‖ ≤ 5 * η / 4) (hremote : 80 * η ≤ ‖s - τ‖) :
    ‖(s - τ)⁻¹‖ ≤ (1 / 64 : ℝ) * ‖(s - ρ)⁻¹‖ := by
  rw [norm_inv, norm_inv]
  have hremote' : 1 / ‖s - τ‖ ≤ 1 / (80 * η) := one_div_le_one_div_of_le (by positivity) hremote
  have hnear' : 1 / (5 * η / 4) ≤ 1 / ‖s - ρ‖ := one_div_le_one_div_of_le (by positivity) hnear
  have hbound : 1 / ‖s - τ‖ ≤ (1 / 64 : ℝ) * (1 / ‖s - ρ‖) := by
    calc
      1 / ‖s - τ‖ ≤ 1 / (80 * η) := hremote'
      _ = (1 / 64 : ℝ) * (1 / (5 * η / 4)) := by
        field_simp; ring
      _ ≤ (1 / 64 : ℝ) * (1 / ‖s - ρ‖) := mul_le_mul_of_nonneg_left hnear' (by norm_num only)
  simpa only [one_div] using hbound

/--
Inputs: a distinguished zero within `5η/4` of the center and a finite family at distance at least
`80η`.
Claim: the remote reciprocal power sum of order `k` is bounded by the family size times the
`k`th power of `1/64` times the distinguished reciprocal norm.
Proof: apply the pointwise separation bound and the finite power-sum norm estimate.
Role: controls the tail after applying the maximum-node theorem to a larger local disk.
-/
theorem norm_sum_remote_reciprocal_powers_le_of_eighty_eta (s ρ : ℂ) (τ : ℕ → ℂ) (m k : ℕ) {η : ℝ}
    (hη : 0 < η) (hnear0 : 0 < ‖s - ρ‖) (hnear : ‖s - ρ‖ ≤ 5 * η / 4)
    (hremote : ∀ j < m, 80 * η ≤ ‖s - τ j‖) :
    ‖∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ k‖ ≤ (m : ℝ) * ((1 / 64 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k := by
  have hbound :=
    norm_sum_powers_le_card_mul_pow_of_norm_le (Finset.range m) (fun j => (s - τ j)⁻¹) k (r :=
      (1 / 64 : ℝ) * ‖(s - ρ)⁻¹‖)
      (by
        intro j hj
        exact
          remote_inv_norm_le_one_sixtyfourth_mul_near_inv_norm s ρ (τ j) hη hnear0 hnear
            (hremote j (Finset.mem_range.mp hj)))
  simpa only [Finset.card_range] using hbound

/--
Inputs: a positive block length `n` and an exponent `k ≥ n`.
Claim: the Kolesnik–Straus coefficient for the choice `M = n` is at least `50⁻ᵏ`.
Proof: use `exp 1 < 3` to bound the coefficient base below by `1/24`, then compare powers.
Role: converts the Kolesnik–Straus estimate into the coarser exponential threshold used by the
zero detector.
-/
theorem ks_coefficient_lower_bound_at_equal_block_lengths (n k : ℕ) (hn : 0 < n) (hk : n ≤ k) :
    ((n : ℝ) / (4 * Real.exp 1 * ((n : ℝ) + n))) ^ n ≥ (1 / (50 : ℝ)) ^ k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hbaseeq : (n : ℝ) / (4 * Real.exp 1 * ((n : ℝ) + n)) = 1 / (8 * Real.exp 1) := by
    field_simp
    ring
  have h24 : (1 / (24 : ℝ)) < 1 / (8 * Real.exp 1) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · nlinarith only [he]
  have hbase : (1 / (50 : ℝ)) ≤ (n : ℝ) / (4 * Real.exp 1 * ((n : ℝ) + n)) := by
    rw [hbaseeq]
    have h50 : (1 / (50 : ℝ)) < 1 / 24 := by norm_num only
    exact le_trans h50.le h24.le
  have hpow : (1 / (50 : ℝ)) ^ k ≤ (1 / (50 : ℝ)) ^ n :=
    pow_le_pow_of_le_one (by norm_num only) (by norm_num only) hk
  exact le_trans hpow (pow_le_pow_left₀ (by norm_num only) hbase n)

/--
Inputs: a positive block length `n` and an exponent `k ≥ n` in the Kolesnik--Straus block with
initial offset `3n`.

Claim: the coefficient `(n / (4e(4n)))^n` is at least `50⁻ᵏ`.

Proof: use `exp 1 < 3` to bound the coefficient base below by `1/48`, then compare powers.

Role: matches the exponent range beginning at `3n + 1` to the `1/50` finite-tail margin.
-/
theorem ks_coefficient_lower_bound_at_triple_block_lengths (n k : ℕ) (hn : 0 < n) (hk : n ≤ k) :
    ((n : ℝ) / (4 * Real.exp 1 * ((n : ℝ) + 3 * n))) ^ n ≥ (1 / (50 : ℝ)) ^ k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hbaseeq : (n : ℝ) / (4 * Real.exp 1 * ((n : ℝ) + 3 * n)) = 1 / (16 * Real.exp 1) := by
    field_simp
    ring
  have h48e : (1 / (48 : ℝ)) < 1 / (16 * Real.exp 1) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · nlinarith only [he]
  have hbase : (1 / (50 : ℝ)) ≤ (n : ℝ) / (4 * Real.exp 1 * ((n : ℝ) + 3 * n)) := by
    rw [hbaseeq]
    have h50 : (1 / (50 : ℝ)) < 1 / 48 := by norm_num only
    exact le_trans h50.le h48e.le
  have hpow : (1 / (50 : ℝ)) ^ k ≤ (1 / (50 : ℝ)) ^ n :=
    pow_le_pow_of_le_one (by norm_num only) (by norm_num only) hk
  exact le_trans hpow (pow_le_pow_left₀ (by norm_num only) hbase n)

/--
Inputs: `m` remote nodes and an exponent at least three times `m`.

Claim: the total remote-to-near ratio `m * (50/64)^k` is at most one half when `k ≥ 3m`.

Proof: write `50/64 = 25/32`, use `(25/32)^3 ≤ 1/2`, and apply `2m ≤ 2^m`.

Role: fixes a concrete exponent budget under which the finite remote tail cannot cancel more than
half of a Kolesnik--Straus main term with base `1/50`.
-/
theorem remote_power_tail_ratio_le_half (m k : ℕ) (hk : 3 * m ≤ k) :
    (m : ℝ) * ((50 : ℝ) / 64) ^ k ≤ 1 / 2 := by
  have htwo : 2 * m ≤ 2 ^ m := Nat.mul_le_pow (by decide) m
  have htwoR : 2 * (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast htwo
  have hden : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hratio : (50 : ℝ) / 64 = 25 / 32 := by norm_num only
  have hthird : (25 / 32 : ℝ) ^ 3 ≤ 1 / 2 := by norm_num only
  have hkdecomp : k = 3 * m + (k - 3 * m) := by omega
  have hthree : ((25 : ℝ) / 32) ^ (3 * m) ≤ (1 / 2 : ℝ) ^ m := by
    have heq : ((25 : ℝ) / 32) ^ (3 * m) = (((25 : ℝ) / 32) ^ 3) ^ m := by rw [pow_mul]
    rw [heq]
    exact pow_le_pow_left₀ (by positivity) hthird m
  have htail : ((25 : ℝ) / 32) ^ (k - 3 * m) ≤ 1 :=
    pow_le_one₀ (by norm_num only) (by norm_num only)
  have hpow : ((50 : ℝ) / 64) ^ k ≤ (1 / 2 : ℝ) ^ m := by
    rw [hkdecomp, hratio, pow_add]
    calc
      ((25 : ℝ) / 32) ^ (3 * m) * ((25 : ℝ) / 32) ^ (k - 3 * m) ≤ (1 / 2 : ℝ) ^ m * 1 :=
        mul_le_mul hthree htail (by positivity) (by positivity)
      _ = (1 / 2 : ℝ) ^ m := mul_one _
  have hratio_final : (m : ℝ) * (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num only, inv_pow, one_div]]
    calc
      (m : ℝ) * (1 / (2 : ℝ) ^ m) = (m : ℝ) / (2 : ℝ) ^ m := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hden).2 (by nlinarith only [htwoR])
  exact le_trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hratio_final

/--
Inputs: a near node, `m` remote nodes at distance at least `80η`, and an exponent `k ≥ 7m`.

Claim: the norm of the remote reciprocal-power sum is at most half the Kolesnik--Straus lower
scale `(‖(s - ρ)⁻¹‖ / 50)^k`.

Proof: combine the pointwise remote-tail estimate with the explicit ratio bound.

Role: supplies the finite tail margin required by the positive zero-detection argument.
-/
theorem norm_sum_remote_reciprocal_powers_le_half_ks_scale (s ρ : ℂ) (τ : ℕ → ℂ) (m k : ℕ) {η : ℝ}
    (hη : 0 < η) (hnear0 : 0 < ‖s - ρ‖) (hnear : ‖s - ρ‖ ≤ 5 * η / 4)
    (hremote : ∀ j < m, 80 * η ≤ ‖s - τ j‖) (hk : 3 * m ≤ k) :
    ‖∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ k‖ ≤ (1 / 2 : ℝ) * ((1 / 50 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k := by
  have htail := norm_sum_remote_reciprocal_powers_le_of_eighty_eta s ρ τ m k hη hnear0 hnear hremote
  have hratio := remote_power_tail_ratio_le_half m k hk
  have hconst : (1 / 50 : ℝ) ^ k * (25 / 32 : ℝ) ^ k = (1 / 64 : ℝ) ^ k := by
    rw [← mul_pow]
    have hbase : (1 / 50 : ℝ) * (25 / 32 : ℝ) = 1 / 64 := by
      field_simp
      ring
    rw [hbase]
  have hscale :
    (m : ℝ) * ((1 / 64 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k =
      ((m : ℝ) * ((50 : ℝ) / 64) ^ k) * ((1 / 50 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k := by
    rw [mul_pow, mul_pow, ← hconst]
    rw [show (50 : ℝ) / 64 = 25 / 32 by norm_num only]
    ring
  calc
    _ ≤ (m : ℝ) * ((1 / 64 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k := htail
    _ ≤ (1 / 2 : ℝ) * ((1 / 50 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k := by
      rw [hscale]
      exact
        mul_le_mul_of_nonneg_right hratio
          (pow_nonneg (mul_nonneg (by norm_num only) (norm_nonneg _)) _)

/--
Inputs: a complex main term and remainder, with a positive lower scale for the main term.

Claim: if the main term reaches the scale and the remainder is at most half that scale, then
their sum has norm at least half the scale.

Proof: apply the reverse triangle inequality and rearrange the two bounds.

Role: combines the maximum-node contribution with the finite remote-zero tail estimate.
-/
theorem norm_add_ge_half_of_main_and_tail (main tail : ℂ) (A : ℝ) (hmain : A ≤ ‖main‖)
    (htail : ‖tail‖ ≤ (1 / 2 : ℝ) * A) : (1 / 2 : ℝ) * A ≤ ‖main + tail‖ := by
  have htriangle : ‖main‖ ≤ ‖main + tail‖ + ‖tail‖ := by
    have heq : main = (main + tail) - tail := by abel
    calc
      ‖main‖ = ‖(main + tail) - tail‖ := congrArg norm heq
      _ ≤ _ := norm_sub_le _ _
  nlinarith only [hmain, htail, htriangle]

/--
Inputs: a finite main sum satisfying the `1/50` Kolesnik--Straus scale and remote nodes at
distance at least `80η`, with exponent `k ≥ 3m`.

Claim: adding the remote reciprocal-power sum preserves at least half of the main lower scale.

Proof: apply the explicit finite-tail estimate and the reverse-triangle combination lemma.

Role: gives the finite-zero version of the positive detection margin once the maximum-node bound
is supplied.
-/
theorem norm_add_remote_reciprocal_powers_ge_half_ks_scale (s ρ main : ℂ) (τ : ℕ → ℂ) (m k : ℕ)
    {η : ℝ} (hη : 0 < η) (hnear0 : 0 < ‖s - ρ‖) (hnear : ‖s - ρ‖ ≤ 5 * η / 4)
    (hremote : ∀ j < m, 80 * η ≤ ‖s - τ j‖) (hk : 3 * m ≤ k)
    (hmain : ((1 / 50 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k ≤ ‖main‖) :
    (1 / 2 : ℝ) * ((1 / 50 : ℝ) * ‖(s - ρ)⁻¹‖) ^ k ≤
      ‖main + ∑ j ∈ Finset.range m, ((s - τ j)⁻¹) ^ k‖ := by
  apply norm_add_ge_half_of_main_and_tail main _ _ hmain
  exact norm_sum_remote_reciprocal_powers_le_half_ks_scale s ρ τ m k hη hnear0 hnear hremote hk

/--
Inputs: nonnegative weights, a summable weighted inverse-square mass, and a uniform bound on the
remote reciprocal terms.
Claim: every weighted reciprocal-power sum of order at least two converges absolutely, with its
norm bounded by the inverse-square mass times the corresponding remote-radius power.
Proof: compare each power with the square times the remaining bounded powers, then sum the norms.
Role: supplies an infinite-tail estimate for the local zero detector.
-/
theorem norm_tsum_weighted_power_le_of_summable_square {ι : Type*} (w : ι → ℝ) (z : ι → ℂ) {R : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hz : ∀ i, ‖z i‖ ≤ R) (hbase : Summable (fun i => w i * ‖z i‖ ^ 2)) (k : ℕ)
    (hk : 2 ≤ k) :
    Summable (fun i => (w i : ℂ) * z i ^ k) ∧
      ‖∑' i, (w i : ℂ) * z i ^ k‖ ≤ R ^ (k - 2) * ∑' i, w i * ‖z i‖ ^ 2 := by
  have hpow (i : ι) : ‖z i‖ ^ k ≤ R ^ (k - 2) * ‖z i‖ ^ 2 := by
    rw [← Nat.sub_add_cancel hk, pow_add]
    simp only [Nat.sub_add_cancel hk]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hz i) _) (sq_nonneg _)
  have hnorm (i : ι) : ‖(w i : ℂ) * z i ^ k‖ = w i * ‖z i‖ ^ k := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i), norm_pow]
  have hscaled : Summable (fun i => R ^ (k - 2) * (w i * ‖z i‖ ^ 2)) := hbase.mul_left _
  have hterm (i : ι) : ‖(w i : ℂ) * z i ^ k‖ ≤ R ^ (k - 2) * (w i * ‖z i‖ ^ 2) := by
    rw [hnorm]
    calc
      w i * ‖z i‖ ^ k ≤ w i * (R ^ (k - 2) * ‖z i‖ ^ 2) := mul_le_mul_of_nonneg_left (hpow i) (hw i)
      _ = R ^ (k - 2) * (w i * ‖z i‖ ^ 2) := by ring
  have hcomplexSummable : Summable (fun i => (w i : ℂ) * z i ^ k) :=
    Summable.of_norm_bounded hscaled hterm
  have hnormSummable : Summable (fun i => ‖(w i : ℂ) * z i ^ k‖) := hcomplexSummable.norm
  refine ⟨hcomplexSummable, ?_⟩
  calc
    ‖∑' i, (w i : ℂ) * z i ^ k‖ ≤ ∑' i, ‖(w i : ℂ) * z i ^ k‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ ≤ ∑' i, R ^ (k - 2) * (w i * ‖z i‖ ^ 2) := by
      apply Summable.tsum_le_tsum
      · exact hterm
      · exact hnormSummable
      · exact hscaled
    _ = R ^ (k - 2) * ∑' i, w i * ‖z i‖ ^ 2 := hbase.tsum_mul_left _

/--
Inputs: a real polynomial and endpoints of a nondegenerate closed interval.

Claim: the affine polynomial mapping `[-1, 1]` to `[a, b]` has degree one and
leading coefficient `(b - a) / 2`.

Proof: compute the degree and leading coefficient of its linear and constant parts.

Role: supports transferring extremal polynomial estimates from `[-1, 1]` to a general interval.
-/
private theorem affine_interval_map_degree_leadingCoeff {a b : ℝ} (hab : a < b) :
    let q := Polynomial.C ((b - a) / 2) * Polynomial.X + Polynomial.C ((a + b) / 2)
    q.natDegree = 1 ∧ q.leadingCoeff = (b - a) / 2 := by
  have hr : (0 : ℝ) < (b - a) / 2 := by linarith only [hab]
  have hrne : (b - a) / 2 ≠ 0 := ne_of_gt hr
  have hdegree :
    (Polynomial.C ((b - a) / 2) * Polynomial.X + Polynomial.C ((a + b) / 2)).natDegree = 1 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_C_mul_X _ hrne
    · rw [Polynomial.natDegree_C, Polynomial.natDegree_C_mul_X _ hrne]
      exact Nat.zero_lt_one
  have hleading :
    (Polynomial.C ((b - a) / 2) * Polynomial.X + Polynomial.C ((a + b) / 2)).leadingCoeff =
      (b - a) / 2 := by
    rw [Polynomial.leadingCoeff_add_of_degree_lt']
    · rw [Polynomial.leadingCoeff_C_mul_X]
    · exact
        lt_of_le_of_lt Polynomial.degree_C_le
          ((WithBot.coe_lt_coe.mpr Nat.zero_lt_one).trans_eq (Polynomial.degree_C_mul_X hrne).symm)
  exact ⟨hdegree, hleading⟩

/--
Inputs: a real polynomial and endpoints of a nondegenerate closed interval.

Claim: composing the polynomial with the affine map from `[-1, 1]` to `[a, b]` preserves
its degree and multiplies its leading coefficient by `((b - a) / 2) ^ p.natDegree`.

Proof: apply the degree and leading-coefficient formulas for polynomial composition.

Role: transports the monic-polynomial extremal estimate on `[-1, 1]` to arbitrary intervals.
-/
private theorem affine_comp_degree_leadingCoeff (p : Polynomial ℝ) {a b : ℝ} (hab : a < b) :
    let q := Polynomial.C ((b - a) / 2) * Polynomial.X + Polynomial.C ((a + b) / 2)
    (p.comp q).natDegree = p.natDegree ∧
      (p.comp q).leadingCoeff = p.leadingCoeff * ((b - a) / 2) ^ p.natDegree := by
  obtain ⟨hqDegree, hqLeadingCoeff⟩ := affine_interval_map_degree_leadingCoeff hab
  refine ⟨?_, ?_⟩
  · rw [Polynomial.natDegree_comp, hqDegree, Nat.mul_one]
  · rw [Polynomial.leadingCoeff_comp
        (by
          rw [hqDegree]; exact Nat.one_ne_zero),
      hqLeadingCoeff]

/--
Inputs: a monic real polynomial and endpoints of a nondegenerate closed interval.

Claim: after the affine change from `[-1, 1]` to `[a, b]`, the polynomial has leading
coefficient `((b - a) / 2) ^ p.natDegree`.

Proof: specialize the affine composition formula to a monic polynomial.

Role: provides the coefficient used with the Chebyshev extremal bound on `[-1, 1]`.
-/
private theorem affine_comp_monic_leadingCoeff (p : Polynomial ℝ) (hp : p.Monic) {a b : ℝ}
    (hab : a < b) :
    let q := Polynomial.C ((b - a) / 2) * Polynomial.X + Polynomial.C ((a + b) / 2)
    (p.comp q).leadingCoeff = ((b - a) / 2) ^ p.natDegree := by
  obtain ⟨_, hleading⟩ := affine_comp_degree_leadingCoeff p hab
  change
    (p.comp (Polynomial.C ((b - a) / 2) * Polynomial.X + Polynomial.C ((a + b) / 2))).leadingCoeff =
      ((b - a) / 2) ^ p.natDegree
  rw [hleading, hp.leadingCoeff, one_mul]

/--
Inputs: a monic real polynomial and endpoints of a nondegenerate interval.

Claim: the polynomial attains at least `((b - a) / 2)^n / 2^(n - 1)` in absolute value
somewhere on `[a, b]`, where `n` is its degree.

Proof: maximize the absolute value on the compact interval, normalize the affine composition,
and apply the Chebyshev coefficient bound to contradict a smaller maximum.

Role: supplies the interval extremal estimate for the second-main-theorem power-sum argument.
-/
private theorem exists_monic_interval_eval_ge {p : Polynomial ℝ} (hp : p.Monic) {a b : ℝ}
    (hab : a < b) :
    ∃ x ∈ Set.Icc a b, ((b - a) / 2) ^ p.natDegree / (2 : ℝ) ^ (p.natDegree - 1) ≤ |p.eval x| := by
  let n := p.natDegree
  let r : ℝ := (b - a) / 2
  let c₀ : ℝ := (a + b) / 2
  let f : ℝ → ℝ := fun x ↦ |p.eval x|
  have hr : 0 < r := by
    dsimp [r]; linarith only [hab]
  have hdPos : 0 < (2 : ℝ) ^ (n - 1) := pow_pos (by norm_num only) _
  let target : ℝ := r ^ n / (2 : ℝ) ^ (n - 1)
  have htPos : 0 < target := div_pos (pow_pos hr _) hdPos
  have hfcont : Continuous f := by
    dsimp [f]
    simpa only [Function.comp_def, Polynomial.eval₂_id] using
      continuous_abs.comp (Polynomial.continuous_eval₂ p (RingHom.id ℝ))
  obtain ⟨xm, hxm, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab.le⟩ hfcont.continuousOn
  let S : ℝ := f xm
  by_contra hnot
  have hSlt : S < target := by
    dsimp [S, f] at hnot ⊢
    by_contra h
    exact hnot ⟨xm, hxm, le_of_not_gt h⟩
  let c : ℝ := (S + target) / 2
  have hSc : S < c := by
    dsimp [c]; linarith only [hSlt]
  have hct : c < target := by
    dsimp [c]; linarith only [hSlt]
  have hSnonneg : 0 ≤ S := abs_nonneg (p.eval xm)
  have hc : 0 < c := by
    dsimp [c]; linarith only [hSnonneg, htPos]
  have hcne : c ≠ 0 := ne_of_gt hc
  let q : Polynomial ℝ := Polynomial.C r * Polynomial.X + Polynomial.C c₀
  let Q : Polynomial ℝ := Polynomial.C c⁻¹ * p.comp q
  have hqeval (u : ℝ) : q.eval u = r * u + c₀ := by
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hleft : c₀ - r = a := by
    dsimp [c₀, r]; ring
  have hright : c₀ + r = b := by
    dsimp [c₀, r]; ring
  have hqmem {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) : q.eval u ∈ Set.Icc a b := by
    rw [hqeval]
    have hmulLo : -r ≤ r * u := by
      calc
        -r = r * (-1) := by ring
        _ ≤ r * u := mul_le_mul_of_nonneg_left hu.1 hr.le
    have hmulHi : r * u ≤ r := by
      calc
        r * u ≤ r * 1 := mul_le_mul_of_nonneg_left hu.2 hr.le
        _ = r := mul_one _
    constructor
    · rw [← hleft]
      linarith only [hmulLo]
    · rw [← hright]
      linarith only [hmulHi]
  have hbound {u : ℝ} (hu : u ∈ Set.Icc (-1) 1) : |Q.eval u| ≤ 1 := by
    have hmaxu : |p.eval (q.eval u)| ≤ S := hmax (hqmem hu)
    rw [show Q.eval u = c⁻¹ * p.eval (q.eval u) by
        simp only [Q, Polynomial.eval_C_mul, Polynomial.eval_comp]]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hc.le)]
    calc
      c⁻¹ * |p.eval (q.eval u)| ≤ c⁻¹ * S := mul_le_mul_of_nonneg_left hmaxu (inv_nonneg.mpr hc.le)
      _ ≤ 1 := by simpa only [div_eq_mul_inv, mul_comm] using (div_le_one hc).2 (le_of_lt hSc)
  have hnQ : Q.natDegree = n := by
    dsimp [Q, n]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hcne), (affine_comp_degree_leadingCoeff p hab).1]
  have hleadQ : Q.leadingCoeff = c⁻¹ * r ^ n := by
    dsimp [Q]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      (affine_comp_degree_leadingCoeff p hab).2, hp.leadingCoeff]
    dsimp [n, r]
    ring
  have hcoeffQ : Q.coeff n = c⁻¹ * r ^ n := by
    calc
      Q.coeff n = Q.coeff Q.natDegree := congrArg (Q.coeff) hnQ.symm
      _ = Q.leadingCoeff := Polynomial.coeff_natDegree
      _ = c⁻¹ * r ^ n := hleadQ
  have hQdeg : Q.degree ≤ n := by
    rw [← hnQ]
    exact Polynomial.degree_le_natDegree
  have hQbound : ∀ u ∈ Set.Icc (-1) 1, |Q.eval u| ≤ 1 := by
    intro u hu
    exact hbound hu
  have hcoeffBound := Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one hQdeg hQbound
  rw [hcoeffQ] at hcoeffBound
  have hcd : c * (2 : ℝ) ^ (n - 1) < r ^ n := (lt_div_iff₀ hdPos).mp hct
  have hstrict : (2 : ℝ) ^ (n - 1) < c⁻¹ * r ^ n := by
    have hDc : (2 : ℝ) ^ (n - 1) * c < r ^ n := by simpa only [mul_comm] using hcd
    have hdiv : (2 : ℝ) ^ (n - 1) < r ^ n / c := (lt_div_iff₀ hc).2 hDc
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  exact (not_lt_of_ge hcoeffBound hstrict)

open Polynomial in
/--
Inputs: a finite family of complex nodes and a nondegenerate real interval.

Claim: some radius in the interval has a product of distances from all node moduli at least
`((b - a) / 2)^n / 2^(n - 1)`, where `n` is the number of nodes.

Proof: form the monic polynomial whose roots are the node moduli and apply the interval
extremal estimate proved from the Chebyshev coefficient bound.

Role: chooses a radius separated collectively from the node moduli for the maximum-node
power-sum estimate.
-/
theorem exists_radius_modulus_product_bound {n : ℕ} (z : Fin n → ℂ) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Set.Icc a b,
      ((b - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) ≤ |∏ i ∈ Finset.univ, (r - ‖z i‖)| := by
  let p : Polynomial ℝ := ∏ i ∈ Finset.univ, (Polynomial.X - Polynomial.C (‖z i‖))
  have hp : p.Monic := by
    dsimp only [p]
    exact Polynomial.monic_prod_X_sub_C (fun i : Fin n ↦ ‖z i‖) Finset.univ
  obtain ⟨r, hr, hbound⟩ := exists_monic_interval_eval_ge hp hab
  have hdeg : p.natDegree = n := by
    dsimp only [p]
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
    simp only [Fintype.card_fin]
  refine ⟨r, hr, ?_⟩
  rw [hdeg] at hbound
  simpa only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using hbound

/--
Inputs: a finite set, a subset, and real factors whose absolute values are at most one.

Claim: the absolute product over the full set is bounded by the absolute product over the subset.

Proof: split the full set into the subset and its complement; the complementary absolute product
is at most one.

Role: removes omitted radial gaps from a full product lower bound when estimating Newton prefixes.
-/
theorem abs_prod_le_abs_prod_of_subset_of_abs_le_one {ι : Type*} (s t : Finset ι) (f : ι → ℝ)
    (ht : t ⊆ s) (hf : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ |∏ i ∈ t, f i| := by
  classical
  rw [Finset.abs_prod, Finset.abs_prod]
  have hdis : Disjoint (s \ t) t :=
    Finset.disjoint_left.mpr
      (by
        intro i hi hti
        exact (Finset.mem_sdiff.mp hi).2 hti)
  have hunion : s \ t ∪ t = s := Finset.sdiff_union_of_subset ht
  rw [← hunion, Finset.prod_union hdis]
  have htail : (∏ i ∈ s \ t, |f i|) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i hi
      exact abs_nonneg _
    · intro i hi
      exact hf i (Finset.sdiff_subset hi)
  calc
    (∏ i ∈ s \ t, |f i|) * (∏ i ∈ t, |f i|) ≤ 1 * (∏ i ∈ t, |f i|) :=
      mul_le_mul_of_nonneg_right htail (Finset.prod_nonneg fun i hi => abs_nonneg _)
    _ = ∏ i ∈ t, |f i| := by simp only [one_mul]

/--
Inputs: a radius in `[0, 1]`, a sequence prefix, and complex nodes in the unit disk.

Claim: the full radial gap product is bounded by the prefix gap product.

Proof: every omitted gap has absolute value at most one, so apply the finite subset product bound.

Role: transfers one Chebyshev radius lower bound to every Newton prefix of the node sequence.
-/
theorem abs_radial_prefix_product_lower_bound {z : ℕ → ℂ} {n k : ℕ} {r : ℝ} (hkn : k ≤ n)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hz : ∀ j < n, ‖z j‖ ≤ 1) :
    |∏ i ∈ Finset.range n, (r - ‖z i‖)| ≤ |∏ i ∈ Finset.range k, (r - ‖z i‖)| := by
  have hsubset : Finset.range k ⊆ Finset.range n := Finset.range_mono hkn
  have hf : ∀ i ∈ Finset.range n, |r - ‖z i‖| ≤ 1 := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [abs_le]
    constructor
    · nlinarith only [hr0, norm_nonneg (z i), hz i hi']
    · nlinarith only [hr1, norm_nonneg (z i)]
  exact
    abs_prod_le_abs_prod_of_subset_of_abs_le_one (Finset.range n) (Finset.range k)
      (fun i => r - ‖z i‖) hsubset hf

/--
Inputs: a finite family of complex nodes in the unit disk and a nonnegative interval endpoint.

Claim: one radius in `[a, 1]` gives the Chebyshev radial lower bound simultaneously for every
subset of the node family.

Proof: choose a radius for the full product and remove omitted factors, each of which has absolute
value at most one.

Role: supplies a common denominator lower bound for all Newton prefixes of normalized nodes.
-/
theorem exists_radius_all_subset_modulus_product_lower_bound {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) (hab : a < 1) :
    ∃ r ∈ Set.Icc a 1,
      ∀ t : Finset (Fin n),
        t ⊆ Finset.univ → ((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) ≤ |∏ i ∈ t, (r - ‖z i‖)| := by
  obtain ⟨r, hr, hfull⟩ := exists_radius_modulus_product_bound z hab
  refine ⟨r, hr, ?_⟩
  intro t ht
  have hgap : ∀ i ∈ Finset.univ, |r - ‖z i‖| ≤ 1 := by
    intro i hi
    rw [abs_le]
    constructor
    · nlinarith only [le_trans ha hr.1, norm_nonneg (z i), hz i]
    · nlinarith only [hr.2, norm_nonneg (z i)]
  have hsubset :=
    abs_prod_le_abs_prod_of_subset_of_abs_le_one Finset.univ t (fun i => r - ‖z i‖) ht hgap
  exact hfull.trans hsubset

/--
Inputs: a finite family of complex nodes in the unit disk and a nonnegative interval endpoint.

Claim: one circle in `[a, 1]` bounds every subset product of complex distances below by the
Chebyshev interval lower bound.

Proof: choose a radius that works for all radial subset products and compare each radial gap with
the corresponding complex distance on the circle.

Role: gives a common contour denominator bound for all Newton prefixes.
-/
theorem exists_circle_all_subset_modulus_product_lower_bound {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) {a : ℝ} (ha : 0 ≤ a) (hab : a < 1) :
    ∃ r ∈ Set.Icc a 1,
      ∀ t : Finset (Fin n),
        t ⊆ Finset.univ →
          ∀ w : ℂ, ‖w‖ = r → ((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) ≤ ‖∏ i ∈ t, (w - z i)‖ := by
  obtain ⟨r, hr, hradial⟩ := exists_radius_all_subset_modulus_product_lower_bound z hz ha hab
  refine ⟨r, hr, ?_⟩
  intro t ht w hw
  have hgap : ∀ i ∈ t, |r - ‖z i‖| ≤ ‖w - z i‖ := by
    intro i hi
    simpa only [hw] using abs_norm_sub_norm_le w (z i)
  have hprod := Finset.prod_le_prod₀ (fun i hi => abs_nonneg (r - ‖z i‖)) hgap
  calc
    ((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) ≤ |∏ i ∈ t, (r - ‖z i‖)| := hradial t ht
    _ = ∏ i ∈ t, |r - ‖z i‖| := Finset.abs_prod _ _
    _ ≤ ∏ i ∈ t, ‖w - z i‖ := hprod
    _ = ‖∏ i ∈ t, (w - z i)‖ := (Complex.norm_prod _ _).symm

/--
Inputs: a complex quotient, an upper bound for the numerator norm, and a positive lower bound for
the denominator norm.

Claim: the quotient norm is bounded by the numerator bound divided by the denominator lower bound.

Proof: apply monotonicity of division in its numerator and denominator separately.

Role: converts contour denominator estimates into pointwise bounds for rational integrands.
-/
theorem norm_div_le_of_norm_le_of_denominator_lower_bound {p q : ℂ} {B δ : ℝ} (hP : ‖p‖ ≤ B)
    (hB : 0 ≤ B) (hδ : 0 < δ) (hQ : δ ≤ ‖q‖) : ‖p / q‖ ≤ B / δ := by
  rw [norm_div]
  calc
    ‖p‖ / ‖q‖ ≤ B / ‖q‖ := div_le_div_of_nonneg_right hP (norm_nonneg q)
    _ ≤ B / δ := div_le_div_of_nonneg_left hB hδ hQ

/--
Inputs: a polynomial with a uniform circle bound, and complex nodes in the unit disk.

Claim: on one Chebyshev-selected circle, the polynomial divided by any subset root product is
bounded by the polynomial bound divided by the radial product lower bound.

Proof: combine the common subset denominator estimate with the pointwise norm-division inequality.

Role: bounds the rational contour integrands used to estimate Newton interpolation coefficients.
-/
theorem exists_circle_all_subset_quotient_bound {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1)
    {a B : ℝ} (ha : 0 ≤ a) (hab : a < 1) (hB : 0 ≤ B) (p : Polynomial ℂ)
    (hP : ∀ r ∈ Set.Icc a 1, ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ≤ B) :
    ∃ r ∈ Set.Icc a 1,
      ∀ t : Finset (Fin n),
        t ⊆ Finset.univ →
          ∀ w : ℂ,
            ‖w‖ = r →
              ‖p.eval w / ∏ i ∈ t, (w - z i)‖ ≤ B / (((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1)) := by
  obtain ⟨r, hr, hQ⟩ := exists_circle_all_subset_modulus_product_lower_bound z hz ha hab
  have hδ : 0 < ((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) := by
    apply div_pos
    · exact pow_pos (div_pos (sub_pos.mpr hab) (by norm_num only)) _
    · exact pow_pos (by norm_num only) _
  refine ⟨r, hr, ?_⟩
  intro t ht w hw
  exact norm_div_le_of_norm_le_of_denominator_lower_bound (hP r hr w hw) hB hδ (hQ t ht w hw)

open Complex in
/--
Inputs: a complex polynomial, a circle, and a point strictly inside the circle.

Claim: the Cauchy integral of the polynomial against the simple-pole kernel equals its value at
the interior point times `2 * π * I`.

Content: identifies the residue contribution of a single interpolation node.

Proof: apply the Cauchy integral formula to the entire function given by polynomial evaluation.

Role: provides the simple-pole extraction step for later contour formulas for Newton coefficients.
-/
theorem circleIntegral_polynomial_eval_sub_inv_mul {p : Polynomial ℂ} {c w : ℂ} {R : ℝ}
    (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ * p.eval z) = (2 * Real.pi * Complex.I) * p.eval w := by
  have hformula :=
    Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (R := R) (c := c) (w :=
      w) (f := fun z : ℂ ↦ p.eval z) (s := ∅) Set.countable_empty hw
      p.differentiable.continuous.continuousOn (fun _ _ ↦ p.differentiableAt)
  simpa only [smul_eq_mul] using hformula

open Complex in
/--
Inputs: a complex polynomial, a circle center, and a nonnegative radius.

Claim: the contour integral of the polynomial around the circle is zero.

Content: removes entire-function terms from later contour decompositions.

Proof: apply Cauchy–Goursat to the entire function given by polynomial evaluation.

Role: removes polynomial terms when reducing a contour expression to its simple-pole part.
-/
theorem circleIntegral_polynomial_eval_eq_zero {p : Polynomial ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    (∮ z in C(c, R), p.eval z) = 0 := by
  exact
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (R := R) hR
      Set.countable_empty p.differentiable.continuous.continuousOn (fun _ _ ↦ p.differentiableAt)

/--
Inputs: a polynomial with a uniform circle bound, and complex nodes in the unit disk.

Claim: on one selected circle, the contour integral of the polynomial divided by any subset root
product is bounded by the circle length times the quotient bound.

Proof: apply the circle integral norm estimate to the pointwise quotient estimate.

Role: supplies integral bounds for the Newton coefficient extraction step.
-/
theorem exists_circle_all_subset_quotient_integral_bound {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) {a B : ℝ} (ha : 0 ≤ a) (hab : a < 1) (hB : 0 ≤ B) (p : Polynomial ℂ)
    (hP : ∀ r ∈ Set.Icc a 1, ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ≤ B) :
    ∃ r ∈ Set.Icc a 1,
      ∀ t : Finset (Fin n),
        t ⊆ Finset.univ →
          ‖∮ w in C(0, r), p.eval w / ∏ i ∈ t, (w - z i)‖ ≤
            2 * Real.pi * r * (B / (((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1))) := by
  obtain ⟨r, hr, hpoint⟩ := exists_circle_all_subset_quotient_bound z hz ha hab hB p hP
  refine ⟨r, hr, ?_⟩
  intro t ht
  apply circleIntegral.norm_integral_le_of_norm_le_const (le_trans ha hr.1)
  intro w hw
  have hw' : ‖w‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hw
  exact hpoint t ht w hw'

/--
Inputs: a finite family of complex nodes, an interval starting at a nonnegative radius, and a
power exponent.

Claim: one radius in `[a, 1]` makes the radial product, multiplied by `r ^ m`, at least `a ^ m`
times the Chebyshev interval lower bound.

Proof: choose the radius from `exists_radius_modulus_product_bound`, then use monotonicity of
natural powers and nonnegativity of the product lower bound.

Role: lets later power-sum estimates trade a radius-dependent factor for an explicit lower endpoint.
-/
theorem exists_scaled_radius_modulus_product_lower_bound_of_interval {n m : ℕ} (z : Fin n → ℂ)
    {a : ℝ} (ha : 0 ≤ a) (hab : a < 1) :
    ∃ r ∈ Set.Icc a 1,
      a ^ m * (((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1)) ≤
        r ^ m * |∏ i ∈ Finset.univ, (r - ‖z i‖)| := by
  obtain ⟨r, hr, hprod⟩ := exists_radius_modulus_product_bound z hab
  refine ⟨r, hr, ?_⟩
  have hpow : a ^ m ≤ r ^ m := pow_le_pow_left₀ ha hr.1 m
  have hfactor : 0 ≤ ((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) := by
    apply div_nonneg
    · exact pow_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (by norm_num only)) _
    · exact pow_nonneg (by norm_num only) _
  calc
    a ^ m * (((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1)) ≤
        r ^ m * (((1 - a) / 2) ^ n / (2 : ℝ) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_right hpow hfactor
    _ ≤ r ^ m * |∏ i ∈ Finset.univ, (r - ‖z i‖)| :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg (le_trans ha hr.1) _)

/--
Inputs: a finite family of complex nodes and a positive node count.

Claim: there is a radius in `[M / (M + n), 1]` for which the radial product multiplied by
`r ^ M` has an explicit lower bound from the Chebyshev interval estimate.

Proof: specialize the interval-scaled estimate at the endpoint `M / (M + n)`.

Role: provides the parameter-dependent radial separation used in the maximal-node Turán step.
-/
theorem exists_scaled_radius_modulus_product_lower_bound_of_order {n M : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n) :
    ∃ r ∈ Set.Icc ((M : ℝ) / ((M : ℝ) + n)) 1,
      ((M : ℝ) / ((M : ℝ) + n)) ^ M *
          ((((1 - (M : ℝ) / ((M : ℝ) + n)) / 2) ^ n) / (2 : ℝ) ^ (n - 1)) ≤
        r ^ M * |∏ i ∈ Finset.univ, (r - ‖z i‖)| := by
  let a : ℝ := (M : ℝ) / ((M : ℝ) + n)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (M : ℝ) + n := by positivity
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (by positivity) hden.le
  have hab : a < 1 := by
    dsimp [a]
    rw [div_lt_one hden]
    linarith only [hnR]
  obtain ⟨r, hr, hbound⟩ :=
    exists_scaled_radius_modulus_product_lower_bound_of_interval (m := M) z ha hab
  refine ⟨r, ?_, ?_⟩
  · simpa only [a] using hr
  · simpa only [a, div_eq_mul_inv, mul_comm] using hbound

/--
Inputs: a finite family of complex nodes and a positive node count.

Claim: one circle with radius in `[M / (M + n), 1]` has the scaled product of distances bounded
below by the Chebyshev interval estimate.

Proof: use the radius from the radial estimate and compare each complex distance with the
corresponding difference of moduli.

Role: supplies a denominator bound on the circle for the subsequent interpolation estimate.
-/
theorem exists_scaled_circle_modulus_product_lower_bound_of_order {n M : ℕ} (z : Fin n → ℂ)
    (hn : 0 < n) :
    ∃ r ∈ Set.Icc ((M : ℝ) / ((M : ℝ) + n)) 1,
      ∀ w : ℂ,
        ‖w‖ = r →
          ((M : ℝ) / ((M : ℝ) + n)) ^ M *
              ((((1 - (M : ℝ) / ((M : ℝ) + n)) / 2) ^ n) / (2 : ℝ) ^ (n - 1)) ≤
            r ^ M * ‖∏ i ∈ Finset.univ, (w - z i)‖ := by
  obtain ⟨r, hr, hradial⟩ := exists_scaled_radius_modulus_product_lower_bound_of_order z hn
  refine ⟨r, hr, ?_⟩
  intro w hw
  have hgap : ∀ i ∈ Finset.univ, |r - ‖z i‖| ≤ ‖w - z i‖ := by
    intro i hi
    simpa only [hw] using abs_norm_sub_norm_le w (z i)
  have hprod : (∏ i ∈ Finset.univ, |r - ‖z i‖|) ≤ ∏ i ∈ Finset.univ, ‖w - z i‖ :=
    Finset.prod_le_prod₀ (fun i hi ↦ abs_nonneg _) hgap
  have hrnonneg : 0 ≤ r := le_trans (div_nonneg (by positivity) (by positivity)) hr.1
  calc
    ((M : ℝ) / ((M : ℝ) + n)) ^ M *
          ((((1 - (M : ℝ) / ((M : ℝ) + n)) / 2) ^ n) / (2 : ℝ) ^ (n - 1)) ≤
        r ^ M * |∏ i ∈ Finset.univ, (r - ‖z i‖)| :=
      hradial
    _ = r ^ M * ∏ i ∈ Finset.univ, |r - ‖z i‖| := by rw [Finset.abs_prod]
    _ ≤ r ^ M * ∏ i ∈ Finset.univ, ‖w - z i‖ :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg hrnonneg M)
    _ = r ^ M * ‖∏ i ∈ Finset.univ, (w - z i)‖ := by rw [← Complex.norm_prod]

/--
Inputs: a finite family of complex nodes and its length `n`.

Claim: a radius `r` between `3/4` and `1` makes `r^(3n)` times the product of radial gaps at
least `40^(-n)`.

Proof: apply the interval extremal bound on `[3/4, 1]`, then use `r ≥ 3/4` to bound the power
factor.

Role: provides the radial denominator estimate for the second-main-theorem power-sum argument.
-/
theorem exists_scaled_radius_modulus_product_lower_bound {n : ℕ} (z : Fin n → ℂ) :
    ∃ r ∈ Set.Icc (3 / 4 : ℝ) 1,
      (1 / 40 : ℝ) ^ n ≤ r ^ (3 * n) * |∏ i ∈ Finset.univ, (r - ‖z i‖)| := by
  obtain ⟨r, hr, hprod⟩ :=
    exists_radius_modulus_product_bound z (a := 3 / 4) (b := 1) (by norm_num only)
  refine ⟨r, hr, ?_⟩
  have hrpow : (27 / 64 : ℝ) ^ n ≤ r ^ (3 * n) := by
    calc
      (27 / 64 : ℝ) ^ n = ((3 / 4 : ℝ) ^ 3) ^ n := by norm_num only
      _ = (3 / 4 : ℝ) ^ (3 * n) := by rw [← pow_mul]
      _ ≤ r ^ (3 * n) := pow_le_pow_left₀ (by norm_num only) hr.1 (3 * n)
  have hprod' : (1 / 16 : ℝ) ^ n ≤ |∏ i ∈ Finset.univ, (r - ‖z i‖)| := by
    have hpow : (2 : ℝ) ^ (n - 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num only) (Nat.sub_le n 1)
    have hcalc : (1 / 16 : ℝ) ^ n * 2 ^ (n - 1) ≤ (1 / 8 : ℝ) ^ n := by
      rw [show (1 / 8 : ℝ) = (1 / 16) * 2 by norm_num only, mul_pow]
      exact mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 16) _)
    have hquot := (le_div_iff₀ (pow_pos (by norm_num only : (0 : ℝ) < 2) _)).mpr hcalc
    have hprodBound : (1 / 8 : ℝ) ^ n / 2 ^ (n - 1) ≤ |∏ i ∈ Finset.univ, (r - ‖z i‖)| := by
      simpa only [show ((1 : ℝ) - 3 / 4) / 2 = (1 / 8 : ℝ) by norm_num only] using hprod
    exact hquot.trans hprodBound
  have hrnonneg : 0 ≤ r := by linarith only [hr.1]
  have hmul :
    (27 / 64 : ℝ) ^ n * (1 / 16 : ℝ) ^ n ≤ r ^ (3 * n) * |∏ i ∈ Finset.univ, (r - ‖z i‖)| :=
    mul_le_mul hrpow hprod' (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 16) _)
      (pow_nonneg hrnonneg _)
  calc
    (1 / 40 : ℝ) ^ n ≤ (27 / 1024 : ℝ) ^ n :=
      pow_le_pow_left₀ (by norm_num only) (by norm_num only) n
    _ = (27 / 64 : ℝ) ^ n * (1 / 16 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num only
    _ ≤ _ := hmul

/--
Inputs: a finite family of complex nodes.

Claim: there is a circle of radius between `3/4` and `1` on which the product polynomial
`∏ i, (w - zᵢ)` has norm at least `40^(-n) r^(-3n)`.

Proof: use the radius with a large product of radial gaps and compare each complex factor with
the corresponding difference of moduli.

Role: supplies the uniform denominator bound for contour estimates in the maximum-node
power-sum theorem.
-/
theorem exists_scaled_circle_product_lower_bound {n : ℕ} (z : Fin n → ℂ) :
    ∃ r ∈ Set.Icc (3 / 4 : ℝ) 1,
      ∀ w : ℂ, ‖w‖ = r → (1 / 40 : ℝ) ^ n ≤ r ^ (3 * n) * ‖∏ i ∈ Finset.univ, (w - z i)‖ := by
  obtain ⟨r, hr, hradial⟩ := exists_scaled_radius_modulus_product_lower_bound z
  refine ⟨r, hr, ?_⟩
  intro w hw
  have hrnonneg : 0 ≤ r := by linarith only [hr.1]
  have hgap : ∀ i ∈ Finset.univ, |r - ‖z i‖| ≤ ‖w - z i‖ := by
    intro i hi
    simpa only [hw] using abs_norm_sub_norm_le w (z i)
  have hprodGap : (∏ i ∈ Finset.univ, |r - ‖z i‖|) ≤ ∏ i ∈ Finset.univ, ‖w - z i‖ :=
    Finset.prod_le_prod₀ (fun i hi ↦ abs_nonneg _) hgap
  calc
    (1 / 40 : ℝ) ^ n ≤ r ^ (3 * n) * |∏ i ∈ Finset.univ, (r - ‖z i‖)| := hradial
    _ = r ^ (3 * n) * ∏ i ∈ Finset.univ, |r - ‖z i‖| := by rw [Finset.abs_prod]
    _ ≤ r ^ (3 * n) * ∏ i ∈ Finset.univ, ‖w - z i‖ :=
      mul_le_mul_of_nonneg_left hprodGap (pow_nonneg hrnonneg _)
    _ = r ^ (3 * n) * ‖∏ i ∈ Finset.univ, (w - z i)‖ := by rw [← Complex.norm_prod]

/--
Inputs: a complex polynomial, a positive circle radius, and a uniform bound for its values on
that circle.

Claim: each coefficient, multiplied by the corresponding power of the radius, is at most the
uniform value bound.

Proof: rescale the polynomial to the unit circle, apply Parseval to its squared norm, and bound
each nonnegative coefficient term by the circle average.

Role: converts the circle estimates for interpolation polynomials into coefficient bounds for
the power-sum identity.
-/
theorem polynomial_coeff_norm_mul_radius_pow_le_of_circle_bound {p : Polynomial ℂ} {r B : ℝ}
    (hr : 0 < r) (hB : 0 ≤ B) (hbound : ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ≤ B) (k : ℕ) :
    ‖p.coeff k‖ * r ^ k ≤ B := by
  let q : Polynomial ℂ := p.comp (Polynomial.C (r : ℂ) * Polynomial.X)
  have hcont : Continuous (fun w : ℂ => ‖q.eval w‖ ^ 2) := by
    exact (continuous_norm.comp (Polynomial.continuous_eval₂ q (RingHom.id ℂ))).pow 2
  have hInt : CircleIntegrable (fun w : ℂ => ‖q.eval w‖ ^ 2) 0 1 :=
    ContinuousOn.circleIntegrable (by norm_num only : (0 : ℝ) ≤ 1) hcont.continuousOn
  have hpoint : ∀ w ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|, ‖q.eval w‖ ^ 2 ≤ B ^ 2 := by
    intro w hw
    have hw' : dist w 0 = |(1 : ℝ)| := by simpa only [Metric.mem_sphere] using hw
    have hwNorm : ‖w‖ = 1 := by
      simpa only [dist_eq_norm, norm_sub_rev, sub_zero,
        abs_of_pos (by norm_num only : (0 : ℝ) < 1)] using hw'
    have hscaled : ‖(r : ℂ) * w‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hwNorm]
      ring
    have heval : q.eval w = p.eval ((r : ℂ) * w) := by
      simp only [q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hvalue : ‖q.eval w‖ ≤ B := by
      rw [heval]
      exact hbound ((r : ℂ) * w) hscaled
    nlinarith only [hvalue, norm_nonneg (q.eval w), hB]
  have havg : Real.circleAverage (fun w : ℂ => ‖q.eval w‖ ^ 2) 0 1 ≤ B ^ 2 :=
    Real.circleAverage_mono_on_of_le_circle hInt hpoint
  have hsum : ∑ i ∈ q.support, ‖q.coeff i‖ ^ 2 ≤ B ^ 2 := by
    rw [Polynomial.sum_sq_norm_coeff_eq_circleAverage]
    exact havg
  have hcoeffSq : ‖q.coeff k‖ ^ 2 ≤ B ^ 2 := by
    by_cases hk : q.coeff k = 0
    · rw [hk, norm_zero]
      nlinarith only [sq_nonneg B]
    · have hmem : k ∈ q.support := Polynomial.mem_support_iff.mpr hk
      exact le_trans (Finset.single_le_sum (fun i hi => sq_nonneg ‖q.coeff i‖) hmem) hsum
  have hnormq : ‖q.coeff k‖ ≤ B := by nlinarith only [hcoeffSq, norm_nonneg (q.coeff k), hB]
  have hcoeffEq : q.coeff k = p.coeff k * (r : ℂ) ^ k := by
    dsimp only [q]
    rw [Polynomial.comp_C_mul_X_coeff]
  rw [hcoeffEq, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hnormq
  exact hnormq

/--
Inputs: a complex polynomial, a circle of radius at least `1/2`, and a uniform value bound on
that circle.

Claim: the coefficient norm sum below any finite cutoff is bounded by the value bound times the
corresponding geometric sum with ratio `2`.

Proof: apply the coefficient estimate from Parseval, lower-bound each radius power by `2⁻ᵏ`,
and sum the resulting coefficientwise inequalities.

Role: turns a circle bound for an interpolation polynomial into the coefficient norm sum needed
by the finite power-sum identity.
-/
theorem sum_range_coeff_norm_le_circle_bound_mul_geom {p : Polynomial ℂ} {r B : ℝ} (hr : 1 / 2 ≤ r)
    (hB : 0 ≤ B) (hbound : ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ≤ B) (m : ℕ) :
    (∑ k ∈ Finset.range m, ‖p.coeff k‖) ≤ B * ∑ k ∈ Finset.range m, (2 : ℝ) ^ k := by
  have hcoeff : ∀ k ∈ Finset.range m, ‖p.coeff k‖ ≤ B * (2 : ℝ) ^ k := by
    intro k hk
    have hck :=
      polynomial_coeff_norm_mul_radius_pow_le_of_circle_bound
        (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hr) hB hbound k
    have hpow : (1 / 2 : ℝ) ^ k ≤ r ^ k := pow_le_pow_left₀ (by norm_num only) hr k
    have hscaled : ‖p.coeff k‖ * (1 / 2 : ℝ) ^ k ≤ B :=
      (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans hck
    have hcancel : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num only [one_pow]
    have hmul := mul_le_mul_of_nonneg_right hscaled (pow_nonneg (by norm_num only : 0 ≤ (2 : ℝ)) k)
    have hmul' : ‖p.coeff k‖ * ((1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k) ≤ B * (2 : ℝ) ^ k := by
      simpa only [mul_assoc, hcancel, mul_one] using hmul
    simpa only [hcancel, mul_one] using hmul'
  calc
    _ ≤ ∑ k ∈ Finset.range m, B * (2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hcoeff k hk
    _ = _ := by rw [← Finset.mul_sum]

open Polynomial in
/--
Inputs: a finite family of complex nodes and a nondegenerate real interval.

Claim: one circle with radius in the interval has the product polynomial
`∏ i, (w - z i)` bounded below in norm by `((b - a) / 2)^n / 2^(n - 1)` at every point
on that circle.

Proof: use the radius with a large product of radial gaps and apply the reverse triangle
inequality to each factor.

Role: supplies the denominator bound for contour estimates in the maximum-node power-sum proof.
-/
theorem exists_circle_modulus_product_lower_bound {n : ℕ} (z : Fin n → ℂ) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Set.Icc a b,
      ∀ w : ℂ,
        ‖w‖ = r → ((b - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) ≤ ‖∏ i ∈ Finset.univ, (w - z i)‖ := by
  obtain ⟨r, hr, hseparation⟩ := exists_radius_modulus_product_bound z hab
  refine ⟨r, hr, ?_⟩
  intro w hw
  calc
    ((b - a) / 2) ^ n / (2 : ℝ) ^ (n - 1) ≤ |∏ i ∈ Finset.univ, (r - ‖z i‖)| := hseparation
    _ = ∏ i ∈ Finset.univ, |r - ‖z i‖| := Finset.abs_prod _ _
    _ ≤ ∏ i ∈ Finset.univ, ‖w - z i‖ :=
      Finset.prod_le_prod₀ (fun i hi ↦ abs_nonneg _) fun i hi ↦ by
        simpa only [hw] using abs_norm_sub_norm_le w (z i)
    _ = ‖∏ i ∈ Finset.univ, (w - z i)‖ := (Complex.norm_prod _ _).symm

/--
Inputs: distinct complex interpolation nodes and prescribed complex values.

Claim: a complex polynomial takes each prescribed value at its corresponding node.

Proof: sum the Lagrange basis polynomials, dividing by their nonzero node-difference products.

Role: constructs the interpolation polynomial used to separate outer nodes in the maximum-node
power-sum estimate.
-/
theorem exists_lagrange_interpolant {n : ℕ} (x y : Fin n → ℂ) (hx : Function.Injective x)
    (hn : 0 < n) : ∃ p : Polynomial ℂ, p.natDegree < n ∧ ∀ k, p.eval (x k) = y k := by
  classical
  let d : Fin n → ℂ := fun i ↦ ∏ j ∈ Finset.univ.erase i, (x i - x j)
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (fun h ↦ hji (hx h).symm)
  let p : Polynomial ℂ :=
    ∑ i : Fin n,
      Polynomial.C (y i / d i) * ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j))
  have hdegree : p.natDegree ≤ n - 1 := by
    dsimp only [p]
    apply Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
    intro i hi
    calc
      (Polynomial.C (y i / d i) *
              ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j))).natDegree ≤
          (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j))).natDegree :=
        Polynomial.natDegree_C_mul_le (y i / d i)
          (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j)))
      _ ≤ ∑ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (x j)).natDegree :=
        Polynomial.natDegree_prod_le (Finset.univ.erase i)
          (fun j => Polynomial.X - Polynomial.C (x j))
      _ = n - 1 := by
        simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_erase_of_mem hi,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rfl
  refine ⟨p, lt_of_le_of_lt hdegree (Nat.sub_lt hn (by norm_num only)), ?_⟩
  intro k
  dsimp only [p]
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single k]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [show (∏ j ∈ Finset.univ.erase k, (x k - x j)) = d k by rfl]
    exact div_mul_cancel₀ _ (hd k)
  · intro i hi hik
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ _⟩)]
    · exact mul_zero _
    · exact sub_self _
  · simp

/--
Inputs: complex nodes and weights, a polynomial whose degree is below a prescribed cutoff, and
its values at those nodes.

Claim: the weighted sum of the prescribed values equals a finite linear combination of the
weighted power sums of the nodes with exponents below the cutoff.

Proof: expand each polynomial evaluation in coefficients, exchange the finite sums, and factor
each coefficient out of the node sum.

Role: converts an interpolation polynomial into the power-sum expression used in the
maximum-node estimate.
-/
theorem weighted_polynomial_interpolation_eq_power_sums {n m : ℕ} (x w y : Fin n → ℂ)
    (p : Polynomial ℂ) (hp : p.natDegree < m) (hpy : ∀ i, p.eval (x i) = y i) :
    (∑ i : Fin n, w i * y i) =
      ∑ k ∈ Finset.range m, p.coeff k * (∑ i : Fin n, w i * (x i) ^ k) := by
  calc
    _ = ∑ i : Fin n, w i * (∑ k ∈ Finset.range m, p.coeff k * (x i) ^ k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hpy i, Polynomial.eval_eq_sum_range' hp]
    _ = ∑ i : Fin n, ∑ k ∈ Finset.range m, p.coeff k * (w i * (x i) ^ k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ Finset.range m, ∑ i : Fin n, p.coeff k * (w i * (x i) ^ k) := by rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range m, p.coeff k * (∑ i : Fin n, w i * (x i) ^ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.mul_sum]

/--
Inputs: distinct complex interpolation nodes, arbitrary node weights and target values, and a
positive number of nodes.

Claim: a polynomial of degree below the node count interpolates the target values, and their
weighted sum is a finite linear combination of weighted power sums.

Proof: construct the Lagrange interpolant and apply the coefficient expansion identity.

Role: packages the distinct-node interpolation step for the maximum-node power-sum argument.
-/
theorem exists_lagrange_power_sum_identity {n : ℕ} (x w y : Fin n → ℂ) (hx : Function.Injective x)
    (hn : 0 < n) :
    ∃ p : Polynomial ℂ,
      p.natDegree < n ∧
        (∀ i, p.eval (x i) = y i) ∧
        (∑ i : Fin n, w i * y i) =
          ∑ k ∈ Finset.range n, p.coeff k * (∑ i : Fin n, w i * (x i) ^ k) := by
  obtain ⟨p, hp, hpy⟩ := exists_lagrange_interpolant x y hx hn
  exact ⟨p, hp, hpy, weighted_polynomial_interpolation_eq_power_sums x w y p hp hpy⟩

/--
Inputs: a finite family of complex nodes, complex weights, and a power exponent.

Claim: the weighted power sum, with repeated nodes included, equals the sum over distinct node
values with the weights in each fiber combined.

Proof: partition the finite index set into the fibers of the node map and replace each node in a
fiber by its common value.

Role: converts repeated-node power sums into weighted sums over distinct nodes for interpolation.
-/
theorem weighted_power_sum_eq_sum_fiberwise {n : ℕ} (z a : Fin n → ℂ) (k : ℕ) :
    (∑ i : Fin n, a i * (z i) ^ k) =
      ∑ ξ ∈ Finset.univ.image z, ∑ i ∈ Finset.univ with z i = ξ, a i * ξ ^ k := by
  classical
  have hgroup :
    (∑ ξ ∈ Finset.univ.image z, ∑ i ∈ Finset.univ with z i = ξ, a i * (z i) ^ k) =
      ∑ i : Fin n, a i * (z i) ^ k :=
    Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image_of_mem z hi)
      (fun i ↦ a i * (z i) ^ k)
  calc
    _ = ∑ ξ ∈ Finset.univ.image z, ∑ i ∈ Finset.univ with z i = ξ, a i * (z i) ^ k := hgroup.symm
    _ = ∑ ξ ∈ Finset.univ.image z, ∑ i ∈ Finset.univ with z i = ξ, a i * ξ ^ k := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

/--
Inputs: a nonempty finite set of complex points and a target function on that set.

Claim: a polynomial of degree below the set's cardinality interpolates the target function.

Proof: enumerate the finite set without repetition and apply the Lagrange interpolation formula.

Role: constructs interpolants after repeated nodes have been reduced to their distinct values.
-/
theorem exists_polynomial_interpolating_finset (s : Finset ℂ) (f : ℂ → ℂ) (hs : 0 < s.card) :
    ∃ p : Polynomial ℂ, p.natDegree < s.card ∧ ∀ ξ ∈ s, p.eval ξ = f ξ := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  let x : Fin s.card → ℂ := fun i ↦ (e.symm i : ℂ)
  let y : Fin s.card → ℂ := fun i ↦ f (x i)
  have hx : Function.Injective x := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  obtain ⟨p, hp, hpy⟩ := exists_lagrange_interpolant x y hx hs
  refine ⟨p, hp, ?_⟩
  intro ξ hξ
  let i : Fin s.card := e ⟨ξ, hξ⟩
  have hxi : x i = ξ := by
    dsimp only [i, x]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨ξ, hξ⟩)
  calc
    p.eval ξ = p.eval (x i) := by rw [hxi]
    _ = y i := hpy i
    _ = f ξ := by
      change f (x i) = f ξ
      rw [hxi]

/--
Inputs: a finite family of complex nodes and weights, a target function on the distinct nodes,
and a nonempty set of node values.

Claim: a polynomial of degree below the number of distinct nodes interpolates the target values,
and the weighted target sum is a finite linear combination of the original weighted power sums.

Proof: interpolate on the finite image of the node map, then apply the coefficient expansion
identity to the original family, including repeated nodes.

Role: connects distinct-node interpolation to the repeated-node maximum-node power-sum estimate.
-/
theorem exists_finset_interpolation_power_sum_identity {n : ℕ} (z w : Fin n → ℂ) (f : ℂ → ℂ)
    (hz : 0 < (Finset.univ.image z).card) :
    ∃ p : Polynomial ℂ,
      p.natDegree < (Finset.univ.image z).card ∧
        (∀ i, p.eval (z i) = f (z i)) ∧
        (∑ i : Fin n, w i * f (z i)) =
          ∑ k ∈ Finset.range (Finset.univ.image z).card,
            p.coeff k * (∑ i : Fin n, w i * (z i) ^ k) := by
  let s : Finset ℂ := Finset.univ.image z
  have hs : 0 < s.card := by simpa only [s] using hz
  obtain ⟨p, hp, hpeval⟩ := exists_polynomial_interpolating_finset s f hs
  have hvalues : ∀ i, p.eval (z i) = f (z i) := by
    intro i
    exact hpeval (z i) (Finset.mem_image_of_mem z (Finset.mem_univ i))
  refine ⟨p, ?_, hvalues, ?_⟩
  · simpa only [s] using hp
  · exact weighted_polynomial_interpolation_eq_power_sums z w (fun i ↦ f (z i)) p hp hvalues

/--
Inputs: nonzero complex nodes and a positive number of nodes.

Claim: the node count is a finite coefficient-weighted combination of the power sums at
exponents `K, ..., K + m - 1`, where `m` is the number of distinct node values. Repeated nodes
are retained through their multiplicities.

Proof: interpolate the inverse `K`th power on the finite image and weight each node by its
`K`th power.

Role: supplies the exact distinct-node interpolation identity needed for the maximum-node
power-sum estimate.
-/
theorem exists_fiberwise_lagrange_power_sum_identity {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, z i ≠ 0)
    (hn : 0 < n) (K : ℕ) :
    ∃ p : Polynomial ℂ,
      p.natDegree < (Finset.univ.image z).card ∧
        (∀ i, p.eval (z i) = (z i)⁻¹ ^ K) ∧
        (n : ℂ) =
          ∑ k ∈ Finset.range (Finset.univ.image z).card,
            p.coeff k * (∑ i : Fin n, z i ^ (K + k)) := by
  let f : ℂ → ℂ := fun ξ => ξ⁻¹ ^ K
  have himage : 0 < (Finset.univ.image z).card := by
    apply Finset.card_pos.mpr
    let i : Fin n := ⟨0, hn⟩
    exact ⟨z i, Finset.mem_image_of_mem z (Finset.mem_univ i)⟩
  obtain ⟨p, hp, hvalues, hidentity⟩ :=
    exists_finset_interpolation_power_sum_identity z (fun i => z i ^ K) f himage
  have hbase : (∑ i : Fin n, z i ^ K * f (z i)) = (n : ℂ) := by
    calc
      _ = ∑ i : Fin n, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [f]
        rw [← mul_pow, mul_inv_cancel₀ (hz i), one_pow]
      _ = (n : ℂ) := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
  refine ⟨p, hp, hvalues, ?_⟩
  calc
    (n : ℂ) = ∑ i : Fin n, z i ^ K * f (z i) := hbase.symm
    _ =
        ∑ k ∈ Finset.range (Finset.univ.image z).card,
          p.coeff k * (∑ i : Fin n, z i ^ K * z i ^ k) :=
      hidentity
    _ = ∑ k ∈ Finset.range (Finset.univ.image z).card, p.coeff k * (∑ i : Fin n, z i ^ (K + k)) :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add]

/--
Inputs: a natural number `k` and a function on pairs of natural numbers.

Claim: summing over the antidiagonal with first coordinate below `k` equals summing over the first
coordinate in `range k`, with the second coordinate determined by the antidiagonal equation.

Proof: reindex by the first coordinate; the antidiagonal equation uniquely determines the second.

Role: puts Newton's power-sum recurrence into the finite range form used for norm estimates.
-/
theorem sum_antidiagonal_filter_fst_lt_eq_range {M : Type} [AddCommMonoid M] (k : ℕ)
    (f : ℕ × ℕ → M) :
    (∑ a ∈ Finset.antidiagonal k with a.1 < k, f a) = ∑ j ∈ Finset.range k, f (j, k - j) := by
  apply
    Finset.sum_bij (s := (Finset.antidiagonal k).filter (fun a => a.1 < k)) (t := Finset.range k)
      (fun a _ => a.1)
  · intro a ha
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  · intro a ha b hb hab
    rcases a with ⟨a₁, a₂⟩
    rcases b with ⟨b₁, b₂⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha hb
    change a₁ = b₁ at hab
    subst b₁
    have hsum : a₁ + a₂ = a₁ + b₂ := ha.1.trans hb.1.symm
    have h₂ : a₂ = b₂ := Nat.add_left_cancel hsum
    subst b₂
    rfl
  · intro j hj
    have hjlt : j < k := Finset.mem_range.mp hj
    refine ⟨(j, k - j), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal]
    constructor
    · exact Nat.add_sub_of_le (Nat.le_of_lt hjlt)
    · exact hjlt
  · intro a ha
    have hmem := Finset.mem_filter.mp ha
    change f a = f (a.1, k - a.1)
    apply congrArg f
    apply Prod.ext
    · rfl
    · have heq : a.2 + a.1 = k := by
        simpa only [Nat.add_comm] using Finset.mem_antidiagonal.mp hmem.1
      exact Nat.eq_sub_of_add_eq (a := k) (b := a.1) (c := a.2) heq

/--
Inputs: a finite family of complex nodes and a natural index.

Claim: the indexed elementary symmetric sum, multiplied by its index, equals the Newton sum of
lower elementary symmetric sums against the power sums of the nodes.

Proof: evaluate the universal multivariate Newton identity at the given complex nodes.

Role: supplies the algebraic recurrence used to derive a maximum-node power-sum lower bound.
-/
theorem finite_power_sum_newton_identity {n : ℕ} (z : Fin n → ℂ) (k : ℕ) :
    (k : ℂ) * (Finset.univ.val.map z).esymm k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ a ∈ Finset.antidiagonal k with a.1 < k,
          (-1 : ℂ) ^ a.1 * (Finset.univ.val.map z).esymm a.1 * (∑ i : Fin n, z i ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval z) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k)
  simpa only [map_mul, map_sum, map_pow, map_natCast, map_neg, map_one,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_sum,
    MvPolynomial.aeval_X] using h

/--
Inputs: a finite family of complex nodes and a natural index.

Claim: the indexed elementary symmetric sum, multiplied by its index, equals the Newton sum over
indices below it, paired with the corresponding power sums.

Proof: reindex the evaluated multivariate Newton identity by the first antidiagonal coordinate.

Role: provides the recurrence in a form suitable for deriving quantitative bounds on elementary
symmetric sums from a common bound on initial power sums.
-/
theorem finite_power_sum_newton_identity_range {n : ℕ} (z : Fin n → ℂ) (k : ℕ) :
    (k : ℂ) * (Finset.univ.val.map z).esymm k =
      (-1 : ℂ) ^ (k + 1) *
        ∑ j ∈ Finset.range k,
          (-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j)) := by
  have h := finite_power_sum_newton_identity z k
  simpa only [sum_antidiagonal_filter_fst_lt_eq_range] using h

/--
Inputs: a finite family of complex nodes and upper bounds for its power sums through order `n`.

Claim: the elementary symmetric sum of order `k ≤ n` has norm at most `2⁻ᵏ` when every positive
power sum of order at most `n` has norm at most `2⁻ᵐ`.

Content: transfers a common geometric bound on power sums to the coefficients of the node
polynomial.

Proof: use Newton's identity at order `k` and inductively bound each term in its finite sum.

Role: supplies the coefficient estimate for detecting a node of maximal norm from its power sums.
-/
theorem norm_esymm_le_half_pow_of_power_sum_bounds {n : ℕ} (z : Fin n → ℂ)
    (hps : ∀ m, 0 < m → m ≤ n → ‖∑ i : Fin n, z i ^ m‖ ≤ (1 / 2 : ℝ) ^ m) :
    ∀ k, k ≤ n → ‖(Finset.univ.val.map z).esymm k‖ ≤ (1 / 2 : ℝ) ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k
      simpa only [Multiset.esymm_zero, norm_one, pow_zero] using le_rfl
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hnewton := finite_power_sum_newton_identity_range z k
      have hmain :
        (k : ℝ) * ‖(Finset.univ.val.map z).esymm k‖ ≤
          ∑ j ∈ Finset.range k,
            ‖(-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ := by
        calc
          _ = ‖(k : ℂ) * (Finset.univ.val.map z).esymm k‖ := by
            simp only [norm_mul, Complex.norm_natCast]
          _ =
              ‖(-1 : ℂ) ^ (k + 1) *
                  ∑ j ∈ Finset.range k,
                    (-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j *
                      (∑ i : Fin n, z i ^ (k - j))‖ :=
            by rw [hnewton]
          _ =
              ‖∑ j ∈ Finset.range k,
                  (-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ :=
            by simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          _ ≤ _ := norm_sum_le _ _
      have hterms :
        ∀ j ∈ Finset.range k,
          ‖(-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ ≤
            (1 / 2 : ℝ) ^ k := by
        intro j hj
        have hjlt : j < k := Finset.mem_range.mp hj
        have hjle : j ≤ k := Nat.le_of_lt hjlt
        have hih := ih j hjlt (le_trans hjle hk)
        have hpower : 0 < k - j := by omega
        have hpowerle : k - j ≤ n := by omega
        have hpsj := hps (k - j) hpower hpowerle
        calc
          _ = ‖(Finset.univ.val.map z).esymm j‖ * ‖∑ i : Fin n, z i ^ (k - j)‖ := by
            simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          _ ≤ (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ (k - j) :=
            mul_le_mul hih hpsj (norm_nonneg _) (pow_nonneg (by norm_num only) _)
          _ = _ := by
            rw [← pow_add]; congr 1; omega
      have hsum :
        ∑ j ∈ Finset.range k,
            ‖(-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ ≤
          (k : ℝ) * (1 / 2 : ℝ) ^ k := by
        calc
          _ ≤ ∑ _j ∈ Finset.range k, (1 / 2 : ℝ) ^ k := Finset.sum_le_sum fun j hj => hterms j hj
          _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
      exact le_of_mul_le_mul_left (hmain.trans hsum) hkR

/--
Inputs: a natural number specifying the length of a finite geometric sum.

Claim: the sum of the first `n` positive powers of `1/2` is strictly less than one.

Proof: rewrite the shifted sum using the finite geometric-series identity and retain its positive
remainder.

Role: provides the strict tail bound in the contradiction argument for a maximal node.
-/
theorem sum_range_half_pow_succ_lt_one (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1)) < 1 := by
  let a : ℝ := 1 / 2
  have hneq : a ≠ 1 := by
    dsimp [a]
    norm_num only
  have hgeom := geom_sum_eq hneq (n + 1)
  have hsplit := Finset.sum_range_succ' (fun j : ℕ => a ^ j) n
  rw [hgeom] at hsplit
  simp only [pow_zero] at hsplit
  have hrewrite : ((a ^ (n + 1) - 1) / (a - 1)) - 1 = 1 - 2 * a ^ (n + 1) := by
    dsimp [a]
    ring
  have hpow : 0 < a ^ (n + 1) :=
    pow_pos
      (by
        dsimp [a]; norm_num only)
      _
  have hval : (∑ j ∈ Finset.range n, a ^ (j + 1)) = 1 - 2 * a ^ (n + 1) := by
    linarith only [hsplit, hrewrite]
  change (∑ j ∈ Finset.range n, a ^ (j + 1)) < 1
  rw [hval]
  linarith only [hpow]

/--
Inputs: a finite family of complex nodes with a selected node of norm one.

Claim: some power sum of order at most the number of nodes has norm at least the corresponding
power of `1/2`.

Proof: assuming all these sums are smaller, Newton's identities bound each elementary symmetric
sum by the matching power of `1/2`. Evaluating the product polynomial at a unit-norm node then
makes the remaining terms have total norm strictly less than its leading term.

Role: gives a spacing-free power-sum lower bound from any selected nonzero node.
-/
theorem exists_power_sum_norm_ge_half_pow_of_node_norm_eq_one {n : ℕ} (z : Fin n → ℂ)
    (hmax : ∃ i, ‖z i‖ = 1) : ∃ k, 0 < k ∧ k ≤ n ∧ (1 / 2 : ℝ) ^ k ≤ ‖∑ i : Fin n, z i ^ k‖ := by
  by_contra h
  have hps : ∀ m, 0 < m → m ≤ n → ‖∑ i : Fin n, z i ^ m‖ ≤ (1 / 2 : ℝ) ^ m := by
    intro m hm hmn
    rcases lt_or_ge (‖∑ i : Fin n, z i ^ m‖) ((1 / 2 : ℝ) ^ m) with hlt | hge
    · exact le_of_lt hlt
    · exact False.elim (h ⟨m, hm, hmn, hge⟩)
  have hesymm := norm_esymm_le_half_pow_of_power_sum_bounds z hps
  obtain ⟨i, hi⟩ := hmax
  let s : Multiset ℂ := Finset.univ.val.map z
  let f : ℕ → ℂ := fun j => (-1 : ℂ) ^ j * (s.esymm j * z i ^ (n - j))
  have hroot : ∑ j ∈ Finset.range (n + 1), f j = 0 := by
    have hprod := Multiset.prod_X_sub_X_eq_sum_esymm s
    have heval := congrArg (Polynomial.eval (z i)) hprod
    have hzmem : z i ∈ s := by exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hmem : 0 ∈ Multiset.map (fun t : ℂ => z i - t) s := by
      apply Multiset.mem_map.mpr
      exact ⟨z i, hzmem, sub_self (z i)⟩
    have hzero : (Multiset.map (fun t : ℂ => z i - t) s).prod = 0 := Multiset.prod_eq_zero hmem
    rw [Polynomial.eval_multiset_prod] at heval
    simp only [Multiset.map_map, Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at heval
    rw [hzero] at heval
    have hncard : s.card = n := by
      simp only [s, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
    rw [hncard] at heval
    simpa only [f, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X] using
      heval.symm
  have hsplit := Finset.sum_range_succ' f n
  rw [hsplit] at hroot
  have htail : (∑ j ∈ Finset.range n, f (j + 1)) = -z i ^ n := by
    simpa only [f, Multiset.esymm_zero, pow_zero, Nat.sub_zero, one_mul] using
      (eq_neg_iff_add_eq_zero.mpr hroot)
  have hnormtail : ‖∑ j ∈ Finset.range n, f (j + 1)‖ = 1 := by
    rw [htail, norm_neg, norm_pow, hi, one_pow]
  have hterm : ∀ j ∈ Finset.range n, ‖f (j + 1)‖ ≤ (1 / 2 : ℝ) ^ (j + 1) := by
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hj1 : j + 1 ≤ n := Nat.succ_le_iff.mpr hjlt
    have hes := hesymm (j + 1) hj1
    have hpow : ‖z i ^ (n - (j + 1))‖ = 1 := by rw [norm_pow, hi, one_pow]
    calc
      ‖f (j + 1)‖ = ‖s.esymm (j + 1)‖ * ‖z i ^ (n - (j + 1))‖ := by
        simp only [f, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      _ = ‖s.esymm (j + 1)‖ := by rw [hpow, mul_one]
      _ ≤ (1 / 2 : ℝ) ^ (j + 1) := hes
  have hupper :
    ‖∑ j ∈ Finset.range n, f (j + 1)‖ ≤ ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, ‖f (j + 1)‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun j hj => hterm j hj
  have hgeom := sum_range_half_pow_succ_lt_one n
  linarith only [hnormtail, hupper, hgeom]

/--
Inputs: a coefficient polynomial, a positive number of moments, and an identity expressing a
positive integer as their coefficient-weighted sum.

Claim: one moment has norm at least the integer divided by the sum of the coefficient norms.

Proof: choose a moment of maximal norm, bound the identity by the triangle inequality, and divide
by the positive coefficient-norm sum.

Role: extracts the quantitative power-sum consequence of the finite interpolation identity.
-/
theorem exists_power_sum_norm_ge_of_coeff_identity {m n : ℕ} (p : Polynomial ℂ) (q : ℕ → ℂ)
    (hm : 0 < m) (hC : 0 < ∑ k ∈ Finset.range m, ‖p.coeff k‖)
    (hid : (n : ℂ) = ∑ k ∈ Finset.range m, p.coeff k * q k) :
    ∃ k ∈ Finset.range m, (n : ℝ) / (∑ j ∈ Finset.range m, ‖p.coeff j‖) ≤ ‖q k‖ := by
  obtain ⟨k, hk, hmax⟩ :=
    (Finset.range m).exists_max_image (fun j => ‖q j‖) (Finset.nonempty_range_iff.mpr (ne_of_gt hm))
  have hnorm : (n : ℝ) ≤ ∑ j ∈ Finset.range m, ‖p.coeff j‖ * ‖q j‖ := by
    calc
      (n : ℝ) = ‖(n : ℂ)‖ := by simp only [Complex.norm_natCast]
      _ = ‖∑ j ∈ Finset.range m, p.coeff j * q j‖ := by rw [hid]
      _ ≤ ∑ j ∈ Finset.range m, ‖p.coeff j * q j‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range m, ‖p.coeff j‖ * ‖q j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [norm_mul]
  have hupper :
    (∑ j ∈ Finset.range m, ‖p.coeff j‖ * ‖q j‖) ≤ ‖q k‖ * (∑ j ∈ Finset.range m, ‖p.coeff j‖) := by
    calc
      _ ≤ ∑ j ∈ Finset.range m, ‖p.coeff j‖ * ‖q k‖ := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hmax j hj) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  exact ⟨k, hk, (div_le_iff₀ hC).mpr (le_trans hnorm hupper)⟩

/--
Inputs: a polynomial representing a positive integer as a coefficient-weighted sum, together
with a uniform bound for the polynomial on a circle of radius at least `1/2`.

Claim: one term in the finite sum has norm at least the integer divided by the circle bound times
the geometric coefficient factor.

Proof: combine the coefficient-sum bound with the maximal-term estimate for a weighted sum.

Role: converts a circle estimate for an interpolation polynomial directly into a power-sum
lower bound.
-/
theorem exists_power_sum_norm_ge_div_circle_bound {m n : ℕ} {p : Polynomial ℂ} {r B : ℝ}
    (hm : 0 < m) (hr : 1 / 2 ≤ r) (hB : 0 ≤ B) (hbound : ∀ w : ℂ, ‖w‖ = r → ‖p.eval w‖ ≤ B)
    (hC : 0 < ∑ k ∈ Finset.range m, ‖p.coeff k‖) (q : ℕ → ℂ)
    (hid : (n : ℂ) = ∑ k ∈ Finset.range m, p.coeff k * q k) :
    ∃ k ∈ Finset.range m, (n : ℝ) / (B * ∑ j ∈ Finset.range m, (2 : ℝ) ^ j) ≤ ‖q k‖ := by
  have hcoef := sum_range_coeff_norm_le_circle_bound_mul_geom hr hB hbound m
  have hden : 0 < B * ∑ j ∈ Finset.range m, (2 : ℝ) ^ j := lt_of_lt_of_le hC hcoef
  obtain ⟨k, hk, hmax⟩ := exists_power_sum_norm_ge_of_coeff_identity p q hm hC hid
  have hratio :
    (n : ℝ) / (B * ∑ j ∈ Finset.range m, (2 : ℝ) ^ j) ≤
      (n : ℝ) / (∑ j ∈ Finset.range m, ‖p.coeff j‖) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg n) hC hcoef
  exact ⟨k, hk, le_trans hratio hmax⟩

/--
Inputs: nonzero complex nodes and a positive number of nodes.

Claim: the Lagrange polynomial for the inverse-power data yields an exponent in the associated
block whose power sum is at least `n` divided by the polynomial's coefficient norm sum.

Proof: the polynomial is nonzero because it interpolates a nonzero value, so its coefficient norm
sum is positive; then apply the coefficient-identity maximum lemma.

Role: converts distinct-node interpolation into an explicit, multiplicity-sensitive power-sum
lower bound, leaving only a quantitative bound on the interpolation coefficients.
-/
theorem exists_fiberwise_power_sum_norm_ge_div_coeff_norm {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0) (hn : 0 < n) (K : ℕ) :
    ∃ p : Polynomial ℂ,
      p.natDegree < (Finset.univ.image z).card ∧
        ∃ k ∈ Finset.range (Finset.univ.image z).card,
          (n : ℝ) / (∑ j ∈ Finset.range (Finset.univ.image z).card, ‖p.coeff j‖) ≤
            ‖∑ i : Fin n, z i ^ (K + k)‖ := by
  obtain ⟨p, hp, hvalues, hidentity⟩ := exists_fiberwise_lagrange_power_sum_identity z hz hn K
  have hidx : ∃ i : Fin n, True := by
    let i : Fin n := ⟨0, hn⟩
    exact ⟨i, trivial⟩
  obtain ⟨i, _⟩ := hidx
  have hvalue : p.eval (z i) ≠ 0 := by
    rw [hvalues i]
    exact pow_ne_zero K (inv_ne_zero (hz i))
  have hpne : p ≠ 0 := by
    intro hp0
    rw [hp0, Polynomial.eval_zero] at hvalue
    exact hvalue rfl
  have hcoeff : p.coeff p.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hC : 0 < ∑ j ∈ Finset.range (Finset.univ.image z).card, ‖p.coeff j‖ := by
    apply Finset.sum_pos'
    · intro j hj
      exact norm_nonneg _
    · exact ⟨p.natDegree, Finset.mem_range.mpr hp, norm_pos_iff.mpr hcoeff⟩
  obtain ⟨k, hk, hbound⟩ :=
    exists_power_sum_norm_ge_of_coeff_identity p (fun k => ∑ i : Fin n, z i ^ (K + k))
      (Finset.card_pos.mpr
        (by
          let i : Fin n := ⟨0, hn⟩
          exact ⟨z i, Finset.mem_image_of_mem z (Finset.mem_univ i)⟩))
      hC hidentity
  exact ⟨p, hp, k, hk, hbound⟩

/--
Inputs: a finite family of complex nodes, an index, and a bound for its first `k` positive power
sums.

Claim: `k` times the norm of the indexed elementary symmetric sum is bounded by the power-sum
bound times the sum of the norms of the preceding elementary symmetric sums.

Proof: take norms in the range form of Newton's identity, apply the triangle inequality, and use
the common power-sum bound term by term.

Role: begins the quantitative implication from small power sums to small elementary symmetric
sums needed for a maximum-node lower bound.
-/
theorem finite_elementary_symm_norm_mul_index_le_power_sum_bound {n : ℕ} (z : Fin n → ℂ) (k : ℕ)
    (B : ℝ) (hB : ∀ j ∈ Finset.range k, ‖∑ i : Fin n, z i ^ (k - j)‖ ≤ B) :
    (k : ℝ) * ‖(Finset.univ.val.map z).esymm k‖ ≤
      B * ∑ j ∈ Finset.range k, ‖(Finset.univ.val.map z).esymm j‖ := by
  have hNewton := finite_power_sum_newton_identity_range z k
  have hnorm :
    (k : ℝ) * ‖(Finset.univ.val.map z).esymm k‖ =
      ‖∑ j ∈ Finset.range k,
          (-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ := by
    calc
      _ = ‖(k : ℂ) * (Finset.univ.val.map z).esymm k‖ := by rw [norm_mul, Complex.norm_natCast]
      _ =
          ‖(-1 : ℂ) ^ (k + 1) *
              ∑ j ∈ Finset.range k,
                (-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ :=
        by rw [hNewton]
      _ = _ := by simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    _ = _ := hnorm
    _ ≤ B * ∑ j ∈ Finset.range k, ‖(Finset.univ.val.map z).esymm j‖ := by
      calc
        _ ≤
            ∑ j ∈ Finset.range k,
              ‖(-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ :=
          norm_sum_le (Finset.range k) (fun j ↦ _)
        _ ≤ ∑ j ∈ Finset.range k, B * ‖(Finset.univ.val.map z).esymm j‖ := by
          apply Finset.sum_le_sum
          intro j hj
          calc
            ‖(-1 : ℂ) ^ j * (Finset.univ.val.map z).esymm j * (∑ i : Fin n, z i ^ (k - j))‖ =
                ‖(Finset.univ.val.map z).esymm j‖ * ‖∑ i : Fin n, z i ^ (k - j)‖ :=
              by
              rw [norm_mul, norm_mul]
              simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
            _ ≤ B * ‖(Finset.univ.val.map z).esymm j‖ := by
              calc
                _ ≤ ‖(Finset.univ.val.map z).esymm j‖ * B :=
                  mul_le_mul_of_nonneg_left (hB j hj)
                    (norm_nonneg ((Finset.univ.val.map z).esymm j))
                _ = _ := by rw [mul_comm]
        _ = _ := by rw [Finset.mul_sum]

/--
Inputs: a finite family of complex nodes with one node equal to `1`.

Claim: the sum of the norms of the positive-degree elementary symmetric sums is at least `1`.

Proof: the root polynomial vanishes at `1`; Vieta's coefficient formula and the triangle
inequality convert this vanishing into the stated lower bound.

Role: contradicts the coefficient smallness that Newton's recurrence would imply if all initial
power sums were small.
-/
theorem finite_elementary_symm_norm_sum_succ_ge_one_of_contains_one {n : ℕ} (z : Fin n → ℂ)
    (i : Fin n) (hi : z i = 1) :
    1 ≤ ∑ k ∈ Finset.range n, ‖(Finset.univ.val.map z).esymm (k + 1)‖ := by
  classical
  let q : Polynomial ℂ := ∏ j : Fin n, (Polynomial.X - Polynomial.C (z j))
  have hcard : (Finset.univ.val.map z).card = n := by
    rw [Multiset.card_map, ← Finset.card_def, Finset.card_univ, Fintype.card_fin]
  have hcoeff :
    ∀ k ≤ n, q.coeff k = (-1 : ℂ) ^ (n - k) * (Finset.univ.val.map z).esymm (n - k) := by
    intro k hk
    have h :=
      Multiset.prod_X_sub_C_coeff (Finset.univ.val.map z)
        (show k ≤ (Finset.univ.val.map z).card by
          rw [hcard]; exact hk)
    simpa only [q, Finset.prod, Multiset.map_map, Function.comp_def, hcard] using h
  have hdegree : q.natDegree = n := by
    dsimp only [q]
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  have hroot : q.eval 1 = 0 := by
    dsimp only [q]
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hi, sub_self]
  have heval : q.eval 1 = ∑ k ∈ Finset.range (n + 1), q.coeff k := by
    rw [Polynomial.eval_eq_sum_range'
        (by
          rw [hdegree]; exact Nat.lt_succ_self n)]
    simp only [one_pow, mul_one]
  have hcoeffsum : (∑ k ∈ Finset.range n, q.coeff k) + 1 = 0 := by
    have h := heval
    rw [hroot, Finset.sum_range_succ] at h
    rw [hcoeff n (le_refl n)] at h
    simp only [Nat.sub_self, pow_zero, one_mul, Multiset.esymm_zero] at h
    exact h.symm
  have hsum : (∑ k ∈ Finset.range n, q.coeff k) = -1 := eq_neg_of_add_eq_zero_left hcoeffsum
  have hnormlower : 1 ≤ ∑ k ∈ Finset.range n, ‖q.coeff k‖ := by
    calc
      1 = ‖(-1 : ℂ)‖ := by rw [norm_neg, norm_one]
      _ = ‖∑ k ∈ Finset.range n, q.coeff k‖ := by rw [← hsum]
      _ ≤ ∑ k ∈ Finset.range n, ‖q.coeff k‖ := norm_sum_le _ _
  have hnormcoeff : ∀ k < n, ‖q.coeff k‖ = ‖(Finset.univ.val.map z).esymm (n - k)‖ := by
    intro k hk
    rw [hcoeff k hk.le, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hreflect :
    (∑ k ∈ Finset.range n, ‖(Finset.univ.val.map z).esymm (n - k)‖) =
      ∑ k ∈ Finset.range n, ‖(Finset.univ.val.map z).esymm (k + 1)‖ := by
    calc
      _ = ∑ j ∈ Finset.range n, ‖(Finset.univ.val.map z).esymm (n - 1 - j + 1)‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < n := Finset.mem_range.mp hj
        have hpos : 0 < n - j := Nat.sub_pos_of_lt hjlt
        have hle : 1 ≤ n - j := Nat.succ_le_iff.mpr hpos
        have hindex : n - 1 - j + 1 = n - j := by
          calc
            n - 1 - j + 1 = n - (1 + j) + 1 := by rw [Nat.sub_sub]
            _ = n - (j + 1) + 1 := by rw [Nat.add_comm 1 j]
            _ = n - j := by
              rw [Nat.sub_succ]
              exact Nat.sub_add_cancel hle
        rw [hindex]
      _ = _ := Finset.sum_range_reflect (fun j ↦ ‖(Finset.univ.val.map z).esymm (j + 1)‖) n
  calc
    1 ≤ ∑ k ∈ Finset.range n, ‖q.coeff k‖ := hnormlower
    _ = ∑ k ∈ Finset.range n, ‖(Finset.univ.val.map z).esymm (n - k)‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hnormcoeff k (Finset.mem_range.mp hk)
    _ = _ := hreflect

/--
Inputs: a finite family of complex nodes containing `1`.

Claim: one of the first `n` positive power sums has norm at least `1 / (4 * n)`.

Proof: if all these power sums were smaller, Newton's recurrence would bound the sum of all
positive-degree elementary symmetric norms by `1 / 3`. The root polynomial vanishes at `1`,
while the preceding coefficient estimate makes that sum at least `1`.

Role: gives a finite block lower bound that can be rescaled at a node of maximal norm.
-/
theorem exists_power_sum_norm_ge_of_contains_one {n : ℕ} (z : Fin n → ℂ) (i : Fin n)
    (hi : z i = 1) : ∃ k ∈ Finset.range n, (1 / (4 * (n : ℝ))) ≤ ‖∑ j : Fin n, z j ^ (k + 1)‖ := by
  classical
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  by_contra hnot
  have hsmall : ∀ k ∈ Finset.range n, ‖∑ j : Fin n, z j ^ (k + 1)‖ < 1 / (4 * (n : ℝ)) := by
    intro k hk
    by_contra hge
    exact hnot ⟨k, hk, le_of_not_gt hge⟩
  let B : ℝ := 1 / (4 * (n : ℝ))
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hfactor : (n : ℝ) * B = 1 / 4 := by
    dsimp only [B]
    calc
      (n : ℝ) * (1 / (4 * (n : ℝ))) = (n : ℝ) / (4 * (n : ℝ)) := by rw [one_div, div_eq_mul_inv]
      _ = 1 / 4 := (div_eq_iff (mul_ne_zero (by norm_num only) hnR)).2 (by ring)
  let e : ℕ → ℝ := fun m ↦ ‖(Finset.univ.val.map z).esymm m‖
  let S : ℝ := ∑ j ∈ Finset.range (n + 1), e j
  let U : ℝ := ∑ k ∈ Finset.range n, e (k + 1)
  have hSdef : S = 1 + U := by
    dsimp only [S, U, e]
    rw [Finset.sum_range_succ']
    simp only [Multiset.esymm_zero, norm_one]
    rw [add_comm]
  have hroot := finite_elementary_symm_norm_sum_succ_ge_one_of_contains_one z i hi
  have hterm : ∀ k ∈ Finset.range n, e (k + 1) ≤ B * S := by
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hkn : k + 1 ≤ n := Nat.succ_le_of_lt hklt
    have hlocal : ∀ j ∈ Finset.range (k + 1), ‖∑ i : Fin n, z i ^ ((k + 1) - j)‖ ≤ B := by
      intro j hj
      have hjlt : j < k + 1 := Finset.mem_range.mp hj
      have hpos : 0 < k + 1 - j := Nat.sub_pos_of_lt hjlt
      have hle : 1 ≤ k + 1 - j := Nat.succ_le_iff.mpr hpos
      let l : ℕ := k + 1 - j - 1
      have hl : l < n := by
        dsimp only [l]
        exact
          lt_of_lt_of_le (Nat.sub_lt hpos (by norm_num only)) (le_trans (Nat.sub_le (k + 1) j) hkn)
      have hpow : l + 1 = (k + 1) - j := by
        dsimp only [l]
        exact Nat.sub_add_cancel hle
      have hbound : ‖∑ i : Fin n, z i ^ (l + 1)‖ ≤ B :=
        le_of_lt (hsmall l (Finset.mem_range.mpr hl))
      rw [hpow] at hbound
      exact hbound
    have hrec := finite_elementary_symm_norm_mul_index_le_power_sum_bound z (k + 1) B hlocal
    have hsubset : Finset.range (k + 1) ⊆ Finset.range (n + 1) := by
      apply Finset.range_subset.mpr
      intro j hj
      exact Finset.mem_range.mpr (lt_trans hj (Nat.lt_succ_of_le hkn))
    have hpref : (∑ j ∈ Finset.range (k + 1), e j) ≤ S := by
      dsimp only [S]
      exact
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (by
            intro j hj hjnot; exact norm_nonneg _)
    have hcast : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
    have hlow : e (k + 1) ≤ ((k + 1 : ℕ) : ℝ) * e (k + 1) := by
      change
        ‖(Finset.univ.val.map z).esymm (k + 1)‖ ≤
          ((k + 1 : ℕ) : ℝ) * ‖(Finset.univ.val.map z).esymm (k + 1)‖
      exact le_mul_of_one_le_left (norm_nonneg _) hcast
    have hupper : ((k + 1 : ℕ) : ℝ) * e (k + 1) ≤ B * (∑ j ∈ Finset.range (k + 1), e j) := by
      change
        ((k + 1 : ℕ) : ℝ) * ‖(Finset.univ.val.map z).esymm (k + 1)‖ ≤
          B * ∑ j ∈ Finset.range (k + 1), ‖(Finset.univ.val.map z).esymm j‖
      exact hrec
    exact le_trans hlow (le_trans hupper (mul_le_mul_of_nonneg_left hpref (le_of_lt hBpos)))
  have hUbound : U ≤ (n : ℝ) * (B * S) := by
    dsimp only [U]
    calc
      _ ≤ ∑ k ∈ Finset.range n, B * S := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (n : ℝ) * (B * S) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSbound : S ≤ 1 + (1 / 4 : ℝ) * S := by
    calc
      S = 1 + U := hSdef
      _ ≤ 1 + (n : ℝ) * (B * S) := by simpa only [add_comm] using add_le_add_right hUbound 1
      _ = 1 + (1 / 4 : ℝ) * S := by rw [← mul_assoc, hfactor]
  have hSup : S ≤ 4 / 3 := by nlinarith only [hSbound]
  have hUup : U ≤ 1 / 3 := by
    calc
      U ≤ (n : ℝ) * (B * S) := hUbound
      _ = (1 / 4 : ℝ) * S := by rw [← mul_assoc, hfactor]
      _ ≤ (1 / 4 : ℝ) * (4 / 3 : ℝ) := mul_le_mul_of_nonneg_left hSup (by norm_num only)
      _ = 1 / 3 := by norm_num only
  have hcontr : U < 1 := lt_of_le_of_lt hUup (by norm_num only)
  exact (not_le_of_gt hcontr) hroot

/--
Inputs: a nonempty finite family of complex nodes.

Claim: one of the first `n` positive power sums is bounded below by `1 / (4 * n)` times the
maximal node norm raised to the same exponent.

Proof: choose a node of maximal norm, normalize it to `1`, apply the preceding finite block
estimate, and rescale the resulting power sum.

Role: provides the maximum-node power-sum estimate for the near-zero contribution to derivative
detection.
-/
theorem exists_max_node_power_sum_norm_ge {n : ℕ} (hn : 0 < n) (z : Fin n → ℂ) :
    ∃ i : Fin n,
      (∀ j, ‖z j‖ ≤ ‖z i‖) ∧
        ∃ k ∈ Finset.range n,
          (1 / (4 * (n : ℝ))) * ‖z i‖ ^ (k + 1) ≤ ‖∑ j : Fin n, z j ^ (k + 1)‖ := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    apply Finset.card_pos.mp
    simpa only [Finset.card_univ, Fintype.card_fin] using hn
  obtain ⟨i, hi, hmax⟩ := Finset.univ.exists_max_image (fun j : Fin n ↦ ‖z j‖) hne
  have hmax' : ∀ j, ‖z j‖ ≤ ‖z i‖ := fun j ↦ hmax j (Finset.mem_univ j)
  by_cases hzero : ‖z i‖ = 0
  · refine ⟨i, hmax', 0, Finset.mem_range.mpr hn, ?_⟩
    rw [hzero]
    simp only [Nat.zero_add, pow_one, mul_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖z i‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hc : z i ≠ 0 := norm_pos_iff.mp hpos
    let w : Fin n → ℂ := fun j ↦ z j / z i
    have hiw : w i = 1 := by
      dsimp only [w]
      exact div_self hc
    obtain ⟨k, hk, hpower⟩ := exists_power_sum_norm_ge_of_contains_one w i hiw
    have hsum : ∑ j : Fin n, w j ^ (k + 1) = (∑ j : Fin n, z j ^ (k + 1)) / (z i) ^ (k + 1) := by
      dsimp only [w]
      calc
        _ = ∑ j : Fin n, z j ^ (k + 1) / (z i) ^ (k + 1) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_pow]
        _ = _ := by rw [Finset.sum_div]
    have hnorm : ‖∑ j : Fin n, w j ^ (k + 1)‖ = ‖∑ j : Fin n, z j ^ (k + 1)‖ / ‖z i‖ ^ (k + 1) := by
      rw [hsum, norm_div, norm_pow]
    rw [hnorm] at hpower
    have hden : 0 < ‖z i‖ ^ (k + 1) := pow_pos hpos _
    have hscaled := (le_div_iff₀ hden).mp hpower
    exact ⟨i, hmax', k, hk, hscaled⟩

/--
Inputs: a nonempty finite index set and a complex node attached to each index.

Claim: a node of maximal norm controls one of the first `s.card` positive power sums by a factor
`1 / (4 * s.card)`.

Proof: enumerate the finite set by `Fin s.card`, apply the indexed maximum-node estimate, and
rewrite the power sum through the enumeration equivalence.

Role: retains repeated node values when finite zero occurrences are indexed by distinct
multiplicity positions.
-/
theorem exists_finset_max_node_power_sum_norm_ge {α : Type*} (s : Finset α) (hs : 0 < s.card)
    (z : α → ℂ) :
    ∃ i ∈ s,
      (∀ j ∈ s, ‖z j‖ ≤ ‖z i‖) ∧
        ∃ k ∈ Finset.range s.card,
          (1 / (4 * (s.card : ℝ))) * ‖z i‖ ^ (k + 1) ≤ ‖∑ j ∈ s, z j ^ (k + 1)‖ := by
  classical
  let e : s ≃ Fin s.card := s.equivFin
  let w : Fin s.card → ℂ := fun i => z (e.symm i).val
  have hsum (k : ℕ) : (∑ j : Fin s.card, w j ^ (k + 1)) = ∑ j ∈ s, z j ^ (k + 1) := by
    calc
      _ = ∑ j : s, z j.val ^ (k + 1) := Equiv.sum_comp e.symm (fun j : s => z j.val ^ (k + 1))
      _ = _ := Finset.sum_coe_sort s (fun j => z j ^ (k + 1))
  obtain ⟨i, hmax, k, hk, hpower⟩ := exists_max_node_power_sum_norm_ge hs w
  let j : α := (e.symm i).val
  have hj : j ∈ s := (e.symm i).property
  have hmax' : ∀ u ∈ s, ‖z u‖ ≤ ‖z j‖ := by
    intro u hu
    simpa only [w, Equiv.symm_apply_apply, j] using hmax (e ⟨u, hu⟩)
  have hnode : w i = z j := by
    change z (e.symm i).val = z (e.symm i).val
    rfl
  refine ⟨j, hj, hmax', k, hk, ?_⟩
  rw [hnode, hsum] at hpower
  exact hpower

/--
Inputs: a finite set of nodes with natural-number multiplicities and positive total multiplicity.

Claim: one node of maximal norm among the repeated occurrences controls one of the first total
multiplicity many weighted power sums by the factor `1 / (4 * totalMultiplicity)`.

Proof: expand each multiplicity into a finite sigma index, apply the finite-set maximum-node
estimate, and rewrite the repeated sum as its multiplicity-weighted form.

Role: converts analytic divisor orders into explicit repeated nodes for local zero detection.
-/
theorem exists_finset_weighted_max_node_power_sum_norm_ge {α : Type*} (s : Finset α)
    (multiplicity : α → ℕ) (z : α → ℂ) (htotal : 0 < ∑ i ∈ s, multiplicity i) :
    ∃ i ∈ s,
      0 < multiplicity i ∧
        (∀ j ∈ s, 0 < multiplicity j → ‖z j‖ ≤ ‖z i‖) ∧
        ∃ k ∈ Finset.range (∑ i ∈ s, multiplicity i),
          (1 / (4 * ((∑ i ∈ s, multiplicity i : ℕ) : ℝ))) * ‖z i‖ ^ (k + 1) ≤
            ‖∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (k + 1)‖ := by
  classical
  let occurrences := s.sigma fun i => Finset.range (multiplicity i)
  let occurrenceNode : (Σ i : α, ℕ) → ℂ := fun x => z x.1
  have hcard : occurrences.card = ∑ i ∈ s, multiplicity i := by
    simp only [occurrences, Finset.card_sigma, Finset.card_range]
  have hsum (k : ℕ) :
    (∑ x ∈ occurrences, occurrenceNode x ^ (k + 1)) =
      ∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (k + 1) := by
    rw [show occurrences = s.sigma (fun i => Finset.range (multiplicity i)) by rfl,
      Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ j ∈ Finset.range (multiplicity i), occurrenceNode ⟨i, j⟩ ^ (k + 1)) =
          ∑ _j ∈ Finset.range (multiplicity i), z i ^ (k + 1) :=
        by
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      _ = (multiplicity i : ℂ) * z i ^ (k + 1) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hoccpos : 0 < occurrences.card := by
    rw [hcard]; exact htotal
  obtain ⟨x, hx, hmax, k, hk, hbound⟩ :=
    exists_finset_max_node_power_sum_norm_ge occurrences hoccpos occurrenceNode
  have hxmem : x.1 ∈ s := (Finset.mem_sigma.mp hx).1
  have hxmultiplicity : 0 < multiplicity x.1 := by
    have hxinner : x.2 ∈ Finset.range (multiplicity x.1) := (Finset.mem_sigma.mp hx).2
    have hxlt := Finset.mem_range.mp hxinner
    omega
  have hmax' : ∀ j ∈ s, 0 < multiplicity j → ‖z j‖ ≤ ‖z x.1‖ := by
    intro j hj hjmult
    have hy : (⟨j, 0⟩ : Σ i : α, ℕ) ∈ occurrences := by
      simp only [occurrences, Finset.mem_sigma]
      exact ⟨hj, Finset.mem_range.mpr hjmult⟩
    exact hmax _ hy
  refine ⟨x.1, hxmem, hxmultiplicity, hmax', k, ?_, ?_⟩
  · simpa only [hcard] using hk
  · rw [show occurrenceNode x = z x.1 by rfl, hsum] at hbound
    simpa only [hcard] using hbound

/--
Inputs: a finite set of complex nodes with natural multiplicities, positive total multiplicity,
and a positive integer block scale.
Claim: a node maximal after taking the block-scale power yields a weighted power-sum lower bound
at some exponent between the scale and the scale times the total multiplicity.
Proof: apply the weighted maximum-node estimate to the powered nodes and combine exponents with
`pow_mul`.
Role: moves the repeated-node Turán estimate to a fixed-multiple high-order block for local zero
detection.
-/
theorem exists_finset_weighted_max_node_power_sum_norm_ge_block {α : Type*} (s : Finset α)
    (multiplicity : α → ℕ) (z : α → ℂ) (htotal : 0 < ∑ i ∈ s, multiplicity i) (K : ℕ) :
    ∃ i ∈ s,
      0 < multiplicity i ∧
        (∀ j ∈ s, 0 < multiplicity j → ‖z j‖ ^ K ≤ ‖z i‖ ^ K) ∧
        ∃ k ∈ Finset.range (∑ i ∈ s, multiplicity i),
          (1 / (4 * ((∑ i ∈ s, multiplicity i : ℕ) : ℝ))) * ‖z i‖ ^ (K * (k + 1)) ≤
            ‖∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (K * (k + 1))‖ := by
  obtain ⟨i, hi, hmi, hmax, k, hk, hpow⟩ :=
    exists_finset_weighted_max_node_power_sum_norm_ge s multiplicity (fun i => z i ^ K) htotal
  refine ⟨i, hi, hmi, ?_, k, hk, ?_⟩
  · simpa only [norm_pow] using hmax
  · simpa only [norm_pow, ← pow_mul] using hpow

/--
Inputs: a finite repeated-node family, a specified positive-weight node, a lower bound for that
node's norm, and a natural block scale.
Claim: some weighted power sum at an exponent from the scaled block retains the specified
node's norm as its lower-bound scale.
Proof: apply the powered maximum-node estimate, compare the specified node with its selected
maximum, and raise the resulting nonnegative inequality to the block index.
Role: carries a known nearby zero through the high-order finite power-sum estimate.
-/
theorem exists_finset_weighted_power_sum_norm_ge_block_of_near {α : Type*} (s : Finset α)
    (multiplicity : α → ℕ) (z : α → ℂ) (htotal : 0 < ∑ i ∈ s, multiplicity i) (ρ : α)
    (hρmem : ρ ∈ s) (hρmult : 0 < multiplicity ρ) (K : ℕ) (r : ℝ) (hr : 0 < r) (hnear : r ≤ ‖z ρ‖) :
    ∃ k ∈ Finset.range (∑ i ∈ s, multiplicity i),
      (1 / (4 * ((∑ i ∈ s, multiplicity i : ℕ) : ℝ))) * r ^ (K * (k + 1)) ≤
        ‖∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (K * (k + 1))‖ := by
  obtain ⟨i, hi, hmi, hmax, k, hk, hbound⟩ :=
    exists_finset_weighted_max_node_power_sum_norm_ge_block s multiplicity z htotal K
  have hnearK : r ^ K ≤ ‖z ρ‖ ^ K := pow_le_pow_left₀ hr.le hnear _
  have hnodeK := hmax ρ hρmem hρmult
  have hri : r ^ K ≤ ‖z i‖ ^ K := hnearK.trans hnodeK
  have hriPow := pow_le_pow_left₀ (by positivity : 0 ≤ r ^ K) hri (k + 1)
  have hriExp : r ^ (K * (k + 1)) ≤ ‖z i‖ ^ (K * (k + 1)) := by simpa only [← pow_mul] using hriPow
  have hN : 0 < ((∑ i ∈ s, multiplicity i : ℕ) : ℝ) := by exact_mod_cast htotal
  have hfactor : 0 ≤ 1 / (4 * ((∑ i ∈ s, multiplicity i : ℕ) : ℝ)) :=
    (one_div_pos.mpr (mul_pos (by norm_num only) hN)).le
  refine ⟨k, hk, ?_⟩
  calc
    _ ≤ (1 / (4 * ((∑ i ∈ s, multiplicity i : ℕ) : ℝ)) * ‖z i‖ ^ (K * (k + 1))) :=
      mul_le_mul_of_nonneg_left hriExp hfactor
    _ ≤ _ := hbound

/--
Inputs: a finite repeated-node family, a nearby node of positive multiplicity, a positive block
scale, and an upper bound for the total multiplicity.

Claim: the selected power-sum exponent lies between the block scale and that scale times the
given multiplicity bound, with the same lower bound at the nearby-node scale.

Proof: apply the block estimate and use the total-multiplicity bound to control its index.

Role: makes the fixed-multiple exponent range explicit for applications with a uniform local
zero-count bound.
-/
theorem exists_finset_weighted_power_sum_norm_ge_fixed_multiple_block_of_near {α : Type*} {C : ℕ}
    (s : Finset α) (multiplicity : α → ℕ) (z : α → ℂ) (htotal : 0 < ∑ i ∈ s, multiplicity i)
    (hcap : ∑ i ∈ s, multiplicity i ≤ C) (ρ : α) (hρmem : ρ ∈ s) (hρmult : 0 < multiplicity ρ)
    (K : ℕ) (r : ℝ) (hr : 0 < r) (hnear : r ≤ ‖z ρ‖) :
    ∃ k ∈ Finset.range (∑ i ∈ s, multiplicity i),
      K ≤ K * (k + 1) ∧
        K * (k + 1) ≤ K * C ∧
        (1 / (4 * ((∑ i ∈ s, multiplicity i : ℕ) : ℝ))) * r ^ (K * (k + 1)) ≤
          ‖∑ i ∈ s, (multiplicity i : ℂ) * z i ^ (K * (k + 1))‖ := by
  obtain ⟨k, hk, hbound⟩ :=
    exists_finset_weighted_power_sum_norm_ge_block_of_near s multiplicity z htotal ρ hρmem hρmult K
      r hr hnear
  have hklt : k < ∑ i ∈ s, multiplicity i := Finset.mem_range.mp hk
  have hindexLower : 1 ≤ k + 1 := Nat.succ_le_iff.mpr (Nat.zero_lt_succ k)
  have hindexUpper : k + 1 ≤ C := Nat.succ_le_iff.mpr (lt_of_lt_of_le hklt hcap)
  refine ⟨k, hk, ?_, ?_, hbound⟩
  · simpa only [Nat.mul_one] using Nat.mul_le_mul_left K hindexLower
  · exact Nat.mul_le_mul_left K hindexUpper

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
