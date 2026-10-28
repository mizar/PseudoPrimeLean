/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.LLS.PairedEulerExcludedBounds
public import PseudoPrime.LLS.TwoPoleSmallPrefixSavings

/-! # Retained real-axis Euler prefixes in signed two-pole witness comparisons -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For Mangoldt-supported paired Euler weights, prime triviality on N-coprime primes and
support coprime to N make the paired prefix exactly twice the principal prefix. Use the exact
excluded-defect identity and the empty excluded support; this covers both full-prime and
odd-prime contradictions. -/
theorem pairedEulerPrefix_eq_twice_of_coprime_support {q N : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (S : Finset ℕ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b) (hcop : ∀ n ∈ S, Nat.Coprime n N)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ S, (1 + (χ n).re) * pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n) =
      2 * ∑ n ∈ S, pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
  classical
  have he :=
    paired_weighted_sum_eq_of_ambient_trivial χ S (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4))
      hS (fun n _ hn ↦ pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _ hn) ht
  have hz :
    excludedCharacterDefect χ N S (pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact False.elim ((Finset.mem_filter.mp hn).2 (hcop n (Finset.mem_filter.mp hn).1))
  rw [hz, sub_zero] at he
  exact he

end PseudoPrime.AnalyticNumberTheory.Arithmetic
