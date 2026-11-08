/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.MRLocalCutoffNumerics

/-! # Uniform Korselt triples and the finite-index threshold -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exceptional squarefree Korselt triple with uniform predecessor valuations.
This predicate packages the arithmetic alternative in the finite-index classification
for use in the nonexceptional witness branch. -/
def UniformKorseltTriple (n : ℕ) : Prop :=
  Squarefree n ∧
    n.primeFactors.card = 3 ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))

/-- At logarithmic scale 100, the input exceeds the cube of the finite-index
threshold. The elementary bound on `log 10` supplies the comparison. -/
theorem ten_pow_27_le_of_log100 {n : ℕ} [NeZero n] (hL : (100 : ℝ) ≤ Real.log n) : 10 ^ 27 ≤ n := by
  by_contra hnot
  have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hnot
  have hcast : (n : ℝ) < (10 : ℝ) ^ 27 := by exact_mod_cast hsmall
  have hlogsmall := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hcast
  have hlog27 : Real.log ((10 : ℝ) ^ 27) < 100 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_lt_seven_thirds]
  exact (not_lt_of_ge hL) (hlogsmall.trans hlog27)

end PseudoPrime.PrimeTestBounds.MillerRabin
