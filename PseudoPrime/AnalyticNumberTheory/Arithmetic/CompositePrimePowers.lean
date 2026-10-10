/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Logarithmic sums on composite prime powers

Vanishing Mangoldt coefficients remove non-prime-powers. Reindexing by prime
and exponent then removes the exponent-one terms selected by primality.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Sum the logarithmic Mangoldt weight on positive nonprime indices up to the cutoff.
Only composite prime powers contribute. This is the arithmetic upper comparison
when a selected residue class contains no primes through the cutoff. -/
noncomputable def compositePrimePowerLogWeightedSum (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime), logWeightedMangoldtTerm x n

/-- The nonprime Mangoldt sum equals the prime-power-supported sum with its prime
terms set to zero. Terms outside prime-power support vanish. This supplies the
input to Chebyshev's prime-power reindexing. -/
theorem compositePrimePowerLogWeightedSum_eq_supported (x : ℝ) :
    compositePrimePowerLogWeightedSum x =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow,
        if ¬n.Prime then logWeightedMangoldtTerm x n else 0 := by
  classical
  unfold compositePrimePowerLogWeightedSum
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : IsPrimePow n
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn, logWeightedMangoldtTerm_eq_zero_of_not_primePow hn, ite_self]

/-- At a nonnegative cutoff, the composite prime-power sum is the double sum of
logarithmic weights with prime exponent at least two. Chebyshev reindexing supplies
the logarithmic exponent cutoff; the prime terms at exponent one vanish.
This separates squares and higher powers in explicit arithmetic bounds. -/
theorem compositePrimePowerLogWeightedSum_eq_sum_powers {x : ℝ} (hx : 0 ≤ x) :
    compositePrimePowerLogWeightedSum x =
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          logWeightedMangoldtTerm x (p ^ k) := by
  classical
  rw [compositePrimePowerLogWeightedSum_eq_supported, Chebyshev.sum_PrimePow_eq_sum_sum _ hx]
  let F := fun k : ℕ ↦
    ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
      if ¬(p ^ k).Prime then logWeightedMangoldtTerm x (p ^ k) else 0
  have he :
    (∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊, F k) =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, F k := by
    apply Finset.sum_subset
    · intro k hk
      obtain ⟨hk2, hkmax⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨(by norm_num only : 1 ≤ 2).trans hk2, hkmax⟩
    · intro k hk hknot
      obtain ⟨hk1, hkmax⟩ := Finset.mem_Icc.mp hk
      have hk2 : ¬2 ≤ k := fun h ↦ hknot (Finset.mem_Icc.mpr ⟨h, hkmax⟩)
      have hk : k = 1 := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hk2)) hk1
      subst k
      apply Finset.sum_eq_zero
      intro p hp
      rw [pow_one, ite_eq_right (not_not.mpr (Finset.mem_filter.mp hp).2)]
  change (∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, F k) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p _
  exact ite_eq_left (Nat.Prime.not_prime_pow (Finset.mem_Icc.mp hk).1)

/-- For a prime and positive exponent, its power's logarithmic weight at a positive
cutoff is the exponent times the prime's weight at the corresponding root cutoff.
Expand the prime-power coefficient and use the logarithm of a real power.
This allows each exponent slice to be bounded by a full Mangoldt sum. -/
theorem logWeightedMangoldtTerm_prime_pow_eq_root {x : ℝ} (hx : 0 < x) {p k : ℕ} (hp : p.Prime)
    (hk : 0 < k) :
    logWeightedMangoldtTerm x (p ^ k) =
      (k : ℝ) * logWeightedMangoldtTerm (x ^ ((1 : ℝ) / k)) p := by
  rw [logWeightedMangoldtTerm_prime_pow hx.ne' hp hk.ne', logWeightedMangoldtTerm,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    Real.log_div (Real.rpow_pos_of_pos hx _).ne' (Nat.cast_ne_zero.mpr hp.ne_zero),
    Real.log_rpow hx]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  field_simp (disch := exact hk0)

/-- For a positive cutoff and exponent, the logarithmic sum over prime powers of that
exponent is bounded by the exponent times the full Mangoldt sum at the root cutoff.
The prime-power identity reduces the claim to adjoining nonnegative composite terms.
This bounds each exponent slice in the composite prime-power decomposition. -/
theorem primePowerExponentSlice_le_logWeightedMangoldtSum {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : 0 < k) :
    (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
        logWeightedMangoldtTerm x (p ^ k)) ≤
      (k : ℝ) * logWeightedMangoldtSum (x ^ ((1 : ℝ) / k)) := by
  calc
    _ =
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          (k : ℝ) * logWeightedMangoldtTerm (x ^ ((1 : ℝ) / k)) p :=
      by
      apply Finset.sum_congr rfl
      intro p hp
      exact logWeightedMangoldtTerm_prime_pow_eq_root hx (Finset.mem_filter.mp hp).2 hk
    _ =
        (k : ℝ) *
          ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
            logWeightedMangoldtTerm (x ^ ((1 : ℝ) / k)) p :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hn _
      exact
        logWeightedMangoldtTerm_nonneg (Real.rpow_pos_of_pos hx _) (Finset.mem_Ioc.mp hn).1
          (Finset.mem_Ioc.mp hn).2

/-- For a cutoff greater than one, the composite contribution is bounded by the sum
of the full Mangoldt sums at all root cutoffs, weighted by their exponents.
Reindex composite prime powers and apply the exponent-slice bound term by term.
This supplies an arithmetic upper bound independent of any Dirichlet character. -/
theorem compositePrimePowerLogWeightedSum_le_root_sums {x : ℝ} (hx : 1 < x) :
    compositePrimePowerLogWeightedSum x ≤
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log 2⌋₊,
        (k : ℝ) * logWeightedMangoldtSum (x ^ ((1 : ℝ) / k)) := by
  rw [compositePrimePowerLogWeightedSum_eq_sum_powers (zero_lt_one.trans hx).le]
  apply Finset.sum_le_sum
  intro k hk
  exact
    primePowerExponentSlice_le_logWeightedMangoldtSum (zero_lt_one.trans hx)
      (lt_of_lt_of_le (by norm_num only : 0 < 2) (Finset.mem_Icc.mp hk).1)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
