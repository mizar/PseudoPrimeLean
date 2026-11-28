/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTrianglePrimeMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters

/-! # Finite triangle mass on common Jacobi signs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At an integer coprime to all three levels the principal term and the
three pair characters sum to four exactly when the local Jacobi signs agree. -/
theorem triangle_pair_indicator (a : ℤ) {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (h₁ : a.gcd p = 1) (h₂ : a.gcd q = 1) (h₃ : a.gcd r = 1) :
    1 + (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq) a).re +
        (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr) a).re +
        (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr) a).re =
      if jacobiSym a p = jacobiSym a q ∧ jacobiSym a q = jacobiSym a r then 4 else 0 := by
  simp only [NumberTheory.complexJacobiNumeratorCharacter_apply_int, jacobiSym.mul_right]
  rcases jacobiSym.eq_one_or_neg_one h₁ with h | h <;>
    rcases jacobiSym.eq_one_or_neg_one h₂ with j | j <;>
    rcases jacobiSym.eq_one_or_neg_one h₃ with k | k <;>
    rw [h, j, k] <;>
    norm_num only [Int.cast_mul, Int.cast_neg, Int.cast_one, Complex.mul_re, Complex.neg_re,
      Complex.neg_im, Complex.one_re, Complex.one_im] <;>
    first
    | rw [ite_eq_left (by decide)]
    | rw [ite_eq_right (by decide)]

/-- On a finite set of units the weighted mass of matching local signs is
one quarter of the principal sum plus the three signed character sums. -/
theorem triangle_pair_indicator_sum {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (s : Finset ℕ) (w : ℕ → ℝ)
    (hc : ∀ n ∈ s, (n : ℤ).gcd p = 1 ∧ (n : ℤ).gcd q = 1 ∧ (n : ℤ).gcd r = 1) :
    let S {k : ℕ} (χ : DirichletCharacter ℂ k) := ∑ n ∈ s, w n * (χ (n : ZMod k)).re
    4 *
        ∑
          n ∈
            s.filter (fun (n : ℕ) => jacobiSym n p = jacobiSym n q ∧ jacobiSym n q = jacobiSym n r),
          w n =
      (∑ n ∈ s, w n) + S (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)) +
        S (NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)) +
        S (NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)) := by
  intro S
  dsimp only [S]
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ←
    Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨ha, hb, hd⟩ := hc n hn
  have h := triangle_pair_indicator (n : ℤ) hp hq hr ha hb hd
  simp only [Int.cast_natCast] at h
  split at h <;> rename_i hh
  · rw [ite_eq_left hh]
    linear_combination -(w n) * h
  · rw [ite_eq_right hh]
    linear_combination -(w n) * h

end PseudoPrime.PrimeTestBounds.MillerRabin
