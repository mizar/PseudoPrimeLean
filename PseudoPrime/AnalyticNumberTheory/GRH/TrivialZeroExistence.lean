/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import PseudoPrime.AnalyticNumberTheory.GRH.TrivialZeros

/-! # Existence of the prescribed trivial zeros, independently of GRH -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- A nonprincipal even character vanishes at every nonpositive even integer.
Primitivity is unnecessary. Split zero from the strictly negative even zeros;
this supplies the even branch of the prescribed trivial-zero set. -/
theorem dirichlet_even_trivial_zero_exists {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) (he : χ.Even) (n : ℕ) : χ.LFunction (-2 * (n : ℂ)) = 0 := by
  cases n with
  | zero =>
    simpa only [Nat.cast_zero, mul_zero] using
      DirichletLFunction.dirichletLFunction_zero_of_even hne he
  | succ n => simpa only [Nat.cast_succ, neg_mul] using he.LFunction_neg_two_mul_nat_add_one n

/-- An odd character vanishes at every negative odd integer. Neither
primitivity nor nonprincipality is needed for this mathlib consequence.
It supplies the odd branch of the prescribed trivial-zero set. -/
theorem dirichlet_odd_trivial_zero_exists {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (ho : χ.Odd) (n : ℕ) : χ.LFunction (-2 * (n : ℂ) - 1) = 0 := by
  simpa only [neg_mul] using ho.LFunction_neg_two_mul_nat_sub_one n

/-- Every prescribed trivial zero of a nonprincipal character is an actual
zero. Primitivity and GRH are unnecessary. Split the parity definition and
apply the preceding existence theorems; this validates the excluded set. -/
theorem LFunction_eq_zero_of_mem_trivialZeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) {z : ℤ} (hz : z ∈ dirichletTrivialZeros χ) : χ.LFunction (z : ℂ) = 0 := by
  have hN := DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hne
  simp only [dirichletTrivialZeros, ite_eq_right hN] at hz
  by_cases ho : χ.Odd
  · rw [ite_eq_left ho] at hz
    obtain ⟨n, rfl⟩ := hz
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast,
      Int.cast_one] using dirichlet_odd_trivial_zero_exists χ ho n
  · rw [ite_eq_right ho] at hz
    obtain ⟨n, rfl⟩ := hz
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast] using
      dirichlet_even_trivial_zero_exists χ hne (χ.even_or_odd.resolve_right ho) n

end PseudoPrime.AnalyticNumberTheory.GRH
