/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GlobalBridge
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Comparator solution: reproduce the challenge statements and use the library proof. -/

@[expose] public section

namespace ComparatorChallenges.PrimeMillerRabinWitness

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

def PrimeMillerRabinWitnessCriterion : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n s d : ℕ,
      1 < n →
        Odd n →
        n - 1 = 2 ^ s * d →
        Odd d →
        ((∀ p : ℕ,
            Nat.Prime p →
              (p : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 →
              ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
          Nat.Prime n)

/-- Under GRH, the prime-base strong test up to the global 0.28 cutoff
characterizes odd primes greater than one. The composite direction requires
the 0.28 rejecting-prime theorem at every logarithmic scale. -/
theorem prime_millerRabin_028_criterion (hGRH : GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ max 2 ((7 / 25 : ℝ) * Real.log n ^ 2) →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  exact PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_028_criterion hGRH hn ho

/-- Under GRH, the prime-base strong test up to the base-nine cutoff characterizes
odd primes greater than one. The 0.28 rejecting-prime bound handles composites;
a direct logarithmic cutoff comparison handles primes. -/
theorem prime_millerRabin_log_nine_criterion (hGRH : GeneralizedRiemannHypothesis) {n : ℕ}
    (hn : 1 < n) (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  exact PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_log_nine_criterion hGRH hn ho

end ComparatorChallenges.PrimeMillerRabinWitness
