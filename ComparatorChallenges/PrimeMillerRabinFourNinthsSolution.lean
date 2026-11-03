/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCriterion
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Comparator solution: reproduce the challenge statements and use the library proof. -/

@[expose] public section

namespace ComparatorChallenges

noncomputable def dirichletTrivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ := by
  classical
    exact
    if q = 1 then {z | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)}
    else if χ.Odd then {z | ∃ n : ℕ, z = -2 * (n : ℤ) - 1} else {z | ∃ n : ℕ, z = -2 * (n : ℤ)}

def DirichletRiemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ,
    χ.LFunction s = 0 → s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ → s.re = (1 : ℝ) / 2

def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → DirichletRiemannHypothesis χ

def PrimeMillerRabinFourNinthsCriterion : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n s d : ℕ,
      1 < n →
        Odd n →
        n - 1 = 2 ^ s * d →
        Odd d →
        ((∀ p : ℕ,
            Nat.Prime p →
              (p : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 →
              ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
          Nat.Prime n)

theorem prime_millerRabin_four_ninths_criterion (hGRH : GeneralizedRiemannHypothesis) {n : ℕ}
    (hn : 1 < n) (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n :=
  PseudoPrime.PrimeTestBounds.MillerRabin.prime_iff_mr_le_four_ninths_log_sq hGRH hn ho

end ComparatorChallenges
