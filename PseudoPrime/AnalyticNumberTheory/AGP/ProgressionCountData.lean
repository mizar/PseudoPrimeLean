/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionAuxiliaryData

/-! # ProgressionCountData

Interfaces connecting uniform progression counts to finite count data.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Purpose: record the quantitative progression-count data that remains to be
constructed from paper95 Theorem 3.1 and reliable Proposition 1.5.

Inputs: a finite set `W` of positive bases and a lower bound `C`.

Fields: a squarefree auxiliary modulus, parameters satisfying the arithmetic
hypotheses of reliable Proposition 1.5, a cutoff above `C`, every base, and
every prime factor of `L`; one parameter coprime to `L`; and the fixed-`k`
count with the source coefficient in residue class `3 mod 4`.

Role: `c₀` and `x₀` are fixed globally in
`AGPProgressionCountDataExists`, as in Proposition 1.5. The theorem
`agp_prime_supply_of_progression_count_data` converts the data into the P3
interface; the structure does not prove that the data exist.
-/
structure AGPProgressionCountData (W : Finset ℕ) (C : ℕ) (c₀ : ℝ) (x₀ : ℕ) where
  L : ℕ
  y : ℕ
  q : ℕ
  x : ℕ
  k : ℕ
  hL : 2 < L
  hSquarefree : Squarefree L
  hLargeEnough : x₀ ≤ x
  hProp15Input : ReliableProp15Admissible L 4 y k x
  hCq : max C (W.sup id) ≤ q
  hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q
  hlambda : 3 ≤ ArithmeticFunction.carmichael L
  hk : 0 < k
  hcoprime : Nat.Coprime k L
  hlower :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) + q : ℕ) : ℝ) <
      reliableProp15Coefficient c₀ 4 x * ((restrictedDivisors L y).card : ℝ)
  hProp15 :
    reliableProp15Coefficient c₀ 4 x * ((restrictedDivisors L y).card : ℝ) ≤
      ((((restrictedDivisors L y).filter
              (fun d => Nat.Prime (d * k + 1) ∧ d * k + 1 ≤ x ∧ (d * k + 1) % 4 = 3)).card :
          ℕ) :
        ℝ)

/--
Assumption: for every finite base set and lower bound, an initial modulus-1
application of Proposition 1.5 supplies auxiliary data whose cutoff is an
exact fifth power with root at least `2 ^ 56`.

Role: this separates auxiliary-parameter selection from the analytic prime
count asserted by `ReliableProp15UniformCount` and makes the dependence on
that initial count explicit.
-/
def AGPProgressionAuxiliaryDataExists (c₀ : ℝ) (xSeed x₀ : ℕ) : Prop :=
  0 < c₀ →
    ReliableProp15UniformCount c₀ 1 1 xSeed →
    ∀ (W : Finset ℕ) (C : ℕ),
      (∀ b ∈ W, 0 < b) →
        ∃ X : ℕ,
          ∃ aux : AGPProgressionAuxiliaryData W C c₀ x₀, 2 ^ 56 ≤ X ∧ aux.x = X ^ 5 ∧ aux.q ≤ X

/--
Assumption: there are fixed constants `c₀ > 0` and `x₀` such that every
positive finite base set and lower bound admits `AGPProgressionCountData` and
a scale `X ≥ 2 ^ 56` whose fifth power is its count cutoff.

Role: this names the analytic interface that remains to be proved
unconditionally and is consumed by `agp_prime_supply_of_progression_count_data`.
-/
def AGPProgressionCountDataExists : Prop :=
  ∃ c₀ : ℝ,
    0 < c₀ ∧
      ∃ x₀ : ℕ,
        2 ≤ x₀ ∧
          ∀ (W : Finset ℕ) (C : ℕ),
            (∀ b ∈ W, 0 < b) →
              ∃ X : ℕ,
                ∃ data : AGPProgressionCountData W C c₀ x₀, 2 ^ 56 ≤ X ∧ data.x = X ^ 5 ∧ data.q ≤ X

end PseudoPrime.AnalyticNumberTheory.AGP
