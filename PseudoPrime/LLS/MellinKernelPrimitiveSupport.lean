/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SubgroupKernelComparison
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Exact nonunit support of primitive Mellin corrections

Before taking absolute values, aggregate the primitive-level correction over
characters. Its finite part is supported exactly on nonunit indices.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For every kernel, scale and index, primitive minus original summand is zero
on units of the level and equals the primitive summand on nonunits.
Apply the exact induced-character value identity; the index-zero case vanishes.
This retains the signed correction without estimating character terms separately. -/
theorem primitive_summand_sub_eq_on_nonunits (K : MellinKernel) {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) :
    K.summand χ.primitiveCharacter x n - K.summand χ x n =
      if Nat.Coprime n q then 0 else K.summand χ.primitiveCharacter x n := by
  by_cases hn : n = 0
  · simp only [summand, hn, ite_true, sub_self, ite_self]
  · rw [summand, summand, ite_eq_right hn, ite_eq_right hn,
      AnalyticNumberTheory.Arithmetic.apply_eq_primitiveCharacter_or_zero χ]
    by_cases hc : Nat.Coprime n q
    · rw [ite_eq_left hc, ite_eq_left hc, sub_self]
    · rw [ite_eq_right hc, ite_eq_right hc, mul_zero, zero_mul, sub_zero]

/-- For finite character and index sets, the aggregate primitive-level
difference equals the primitive sum restricted to nonunit indices.
Interchange the finite sums and apply the pointwise value identity.
This exposes the local aggregate whose sign enters the fixed-kernel comparison. -/
theorem sum_primitive_difference_eq_nonunit_sum (K : MellinKernel) {q : ℕ}
    (A : Finset (DirichletCharacter ℂ q)) (I : Finset ℕ) (x : ℝ) :
    ∑ χ ∈ A, ∑ n ∈ I, (K.summand χ.primitiveCharacter x n - K.summand χ x n) =
      ∑ n ∈ I.filter (fun n ↦ ¬Nat.Coprime n q), ∑ χ ∈ A, K.summand χ.primitiveCharacter x n := by
  classical
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : Nat.Coprime n q
  · simp only [primitive_summand_sub_eq_on_nonunits, ite_eq_left hc, Finset.sum_const_zero,
      ite_eq_right (not_not.mpr hc)]
  · simp only [primitive_summand_sub_eq_on_nonunits, ite_eq_right hc, ite_eq_left hc]

/-- If every prime-power index in the finite cutoff is coprime to the level,
the aggregate primitive-level correction is zero for any finite character set.
Restrict to nonunits and use the Mangoldt support of kernel summands.
This removes the finite local contribution under a coprime prime-power cutoff. -/
theorem sum_primitive_difference_eq_zero_of_primePow_coprime (K : MellinKernel) {q : ℕ}
    (A : Finset (DirichletCharacter ℂ q)) (I : Finset ℕ) (x : ℝ)
    (hcop : ∀ n ∈ I, IsPrimePow n → Nat.Coprime n q) :
    ∑ χ ∈ A, ∑ n ∈ I, (K.summand χ.primitiveCharacter x n - K.summand χ x n) = 0 := by
  classical
  rw [sum_primitive_difference_eq_nonunit_sum]
  apply Finset.sum_eq_zero
  intro n hn
  have hmem := Finset.mem_filter.mp hn
  have hnp : ¬IsPrimePow n := fun hp ↦ hmem.2 (hcop n hmem.1 hp)
  apply Finset.sum_eq_zero
  intro χ _
  exact summand_eq_zero_of_not_primePow K χ.primitiveCharacter x hnp

/-- If every prime divisor of the level is larger than a finite cutoff B,
the primitive-level correction on 1≤n≤B vanishes for any finite character set.
A common prime divisor of n and q would be at most n≤B, contradicting the hypothesis.
This supplies the finite local cancellation from the no-small-divisor condition
used in the Miller–Rabin contradiction. -/
theorem sum_primitive_difference_eq_zero_of_no_small_prime_divisor (K : MellinKernel) {q B : ℕ}
    (A : Finset (DirichletCharacter ℂ q)) (x : ℝ) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → B < p) :
    ∑ χ ∈ A, ∑ n ∈ Finset.Ioc 0 B, (K.summand χ.primitiveCharacter x n - K.summand χ x n) = 0 := by
  apply sum_primitive_difference_eq_zero_of_primePow_coprime
  intro n hn _
  apply Classical.byContradiction
  intro hc
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  exact
    (not_lt_of_ge ((Nat.le_of_dvd (Finset.mem_Ioc.mp hn).1 hpn).trans (Finset.mem_Ioc.mp hn).2))
      (hdiv p hp hpq)

/-- For every nonzero level, the primitive source of the principal Mellin
summand equals the level-one principal summand at every scale and index.
Its conductor is one and every residue there is a unit.
This shared identity removes dependent-level casts in principal comparisons. -/
theorem principal_primitive_summand_eq_level_one (K : MellinKernel) {q : ℕ} [NeZero q] (x : ℝ)
    (n : ℕ) :
    K.summand (1 : DirichletCharacter ℂ q).primitiveCharacter x n =
      K.summand (1 : DirichletCharacter ℂ 1) x n := by
  have hn : IsUnit (n : ZMod ((1 : DirichletCharacter ℂ q).conductor)) := by
    rw [DirichletCharacter.conductor_one]
    exact isUnit_of_subsingleton _
  rw [summand, summand, DirichletCharacter.primitiveCharacter_one, MulChar.one_apply hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]

/-- If every prime divisor of the level exceeds the cutoff B, the finite
principal Mellin sum on 1≤n≤B equals the level-one sum, at any real scale.
Apply finite primitive-correction cancellation to the singleton principal
character and identify its primitive summands. This eliminates finite modulus loss. -/
theorem principal_sum_eq_level_one_of_no_small_prime_divisor (K : MellinKernel) {q B : ℕ} [NeZero q]
    (x : ℝ) (hdiv : ∀ p : ℕ, p.Prime → p ∣ q → B < p) :
    (∑ n ∈ Finset.Ioc 0 B, K.summand (1 : DirichletCharacter ℂ q) x n) =
      ∑ n ∈ Finset.Ioc 0 B, K.summand (1 : DirichletCharacter ℂ 1) x n := by
  have h :=
    sum_primitive_difference_eq_zero_of_no_small_prime_divisor K
      ({(1 : DirichletCharacter ℂ q)} : Finset (DirichletCharacter ℂ q)) x hdiv
  simp only [Finset.sum_singleton, principal_primitive_summand_eq_level_one,
    Finset.sum_sub_distrib] at h
  exact (sub_eq_zero.mp h).symm

end PseudoPrime.LLS.PaperStatements.MellinKernel
