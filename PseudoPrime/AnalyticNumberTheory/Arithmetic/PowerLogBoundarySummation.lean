/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogWeightedSummation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds

/-! # Exact Chebyshev boundary terms for power-weighted partial summation -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The ordinary power-log boundary sum at a cutoff is the power weight
times psi plus sigma times the actual logarithmically weighted sum.
The vanishing Mangoldt term at zero matches the positive-prefix convention. -/
theorem power_boundary_sum_eq (σ b : ℝ) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m * (b ^ (-σ) * (1 + σ * Real.log (b / m)))) =
      b ^ (-σ) * (Chebyshev.psi b + σ * logWeightedMangoldtSum b) := by
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _),
    ArithmeticFunction.map_zero, add_zero]
  simp only [logWeightedMangoldtSum, logWeightedMangoldtTerm, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m hm ↦ by ring)

/-- Split any finite sum at a real cutoff between zero and the upper cutoff.
Both intervals include their upper endpoint, so the tail is open at the
lower cutoff. This preserves prime-power contributions at both boundaries. -/
theorem power_prefix_sum_split {a b : ℝ} (hab : a ≤ b) (F : ℕ → ℝ) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, F m) =
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, F m) + ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, F m := by
  have hd : Disjoint (Finset.Ioc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊) :=
    Finset.disjoint_left.mpr
      (fun m hm ht ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp ht).1)
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab), Finset.sum_union hd]

/-- The lower clipped endpoint splits into its exact Chebyshev boundary
and the finite power-weighted tail. Below the lower cutoff the maximum
is the cutoff; above it the logarithm at the atom is zero. -/
theorem power_clipped_lower_boundary_sum_eq (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ioc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt m *
          ((max a (m : ℝ)) ^ (-σ) * (1 + σ * Real.log (max a (m : ℝ) / m)))) =
      a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) +
        ∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ) := by
  rw [power_prefix_sum_split hab]
  have hp :
    (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊,
        ArithmeticFunction.vonMangoldt m *
          ((max a (m : ℝ)) ^ (-σ) * (1 + σ * Real.log (max a (m : ℝ) / m)))) =
      a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) := by
    rw [← power_boundary_sum_eq σ a]
    exact
      Finset.sum_congr rfl
        (fun m hm ↦ by rw [max_eq_left ((Nat.le_floor_iff ha.le).mp (Finset.mem_Ioc.mp hm).2)])
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  rw [max_eq_right ((Nat.floor_lt ha.le).mp (Finset.mem_Ioc.mp hm).1).le, Real.log_div_self,
    mul_zero, add_zero, mul_one]

/-- On a positive finite interval, the power-weighted Mangoldt tail
equals the logarithmic integral minus the lower Chebyshev boundary and
plus the upper boundary. This exact formula is the input to the infinite
tail limit and retains an open lower and closed upper arithmetic cutoff. -/
theorem power_mangoldt_tail_eq_log_integral (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) =
      (∫ t in a..b, logWeightedMangoldtSum t * (σ ^ 2 * t ^ (-σ - 1))) -
          a ^ (-σ) * (Chebyshev.psi a + σ * logWeightedMangoldtSum a) +
        b ^ (-σ) * (Chebyshev.psi b + σ * logWeightedMangoldtSum b) := by
  have h := power_logWeightedMangoldtSum_integral_eq σ ha hab
  simp only [mul_sub] at h
  rw [Finset.sum_sub_distrib, power_clipped_lower_boundary_sum_eq σ ha hab,
    power_boundary_sum_eq σ b] at h
  linarith only [h]

/-- The actual Mangoldt power weight is summable for sigma greater than
one. Rewrite the reciprocal real power to the proved Dirichlet-series
summability theorem. This provides the arithmetic tail limit. -/
theorem summable_powerMangoldtWeight {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun m : ℕ ↦ ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) := by
  have he :
    (fun m : ℕ ↦ ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) =
      (fun m : ℕ ↦ ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ) := by
    funext m
    rw [Real.rpow_neg (Nat.cast_nonneg m), div_eq_mul_inv]
  rw [he]
  exact summable_vonMangoldt_div_rpow hσ

/-- Positive integer prefixes of the power-weighted Mangoldt sum converge
to its total series. Shift the range by one and remove the vanishing
Mangoldt term at zero to match the positive-prefix convention. -/
theorem tendsto_powerMangoldtPrefix {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ))
      Filter.atTop (nhds (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ))) := by
  have ht :=
    (summable_powerMangoldtWeight hσ).hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  apply Filter.Tendsto.congr (fun n ↦ ?_) ht
  dsimp only [Function.comp_apply]
  rw [Nat.range_eq_Icc_zero_sub_one (n + 1) (Nat.add_one_ne_zero n), Nat.add_sub_cancel, ←
    Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le n)]
  simp only [ArithmeticFunction.map_zero, zero_mul, add_zero]

/-- A power-weighted tail with fixed real lower cutoff converges to the
total series minus the retained prefix. Split the positive intervals at
the natural floor, preserving the open lower arithmetic endpoint. -/
theorem tendsto_powerMangoldtTailPrefix {σ : ℝ} (hσ : 1 < σ) (a : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∑ m ∈ Finset.Ioc ⌊a⌋₊ n, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ))
      Filter.atTop
      (nhds
        ((∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) -
          ∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ))) := by
  have ht :=
    (tendsto_powerMangoldtPrefix hσ).sub_const
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ))
  apply Filter.Tendsto.congr' ?_ ht
  apply (Filter.eventually_ge_atTop ⌊a⌋₊).mono
  intro n hn
  have hd : Disjoint (Finset.Ioc 0 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ n) :=
    Finset.disjoint_left.mpr
      (fun m hm ht ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp ht).1)
  have he := Finset.sum_union (f := fun m ↦ ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-σ)) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hn] at he
  dsimp only
  linarith only [he]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
