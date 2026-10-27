/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FixedSquarefreeCubicBounds
public import PseudoPrime.NumberTheory.SpecifiedJacobiDecomposition

/-! # Least witnesses for a prescribed fixed squarefree-part family -/

public section

namespace PseudoPrime.PseudoSquare

/-- For a prescribed odd nonsquare n=s²d with squarefree d>1, GRH and the
absence of negative prime divisors of s below the fixed radius produce an
odd coprime negative prime within that radius. Construct character data
with the prescribed factors, so the bound depends only on d. -/
theorem exists_prime_neg_one_le_fixed_squarefree_family {n d s : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hd : 1 < d) (hsf : Squarefree d) (hdec : s ^ 2 * d = n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ s → jacobiSym d p = -1 → fixedSquarefreeCubicBound d < p) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ fixedSquarefreeCubicBound d := by
  obtain ⟨bridge, he, hs⟩ :=
    NumberTheory.exists_jacobiCharacterArithmeticData_of_sq_mul hn hns hd hsf hdec
  have hl :
    ∀ p : ℕ,
      p.Prime →
        p ∣ bridge.squareFactor →
        jacobiSym bridge.squarefreePart p = -1 →
        fixedSquarefreeCubicBound bridge.squarefreePart < p := by
    simpa only [he, hs] using hlarge
  simpa only [he] using exists_prime_neg_one_le_fixed_squarefree_cubic_bound bridge hGRH hl

/-- The fixed squarefree-family bound controls the least negative odd-prime
witness. Apply the family existence theorem and leastness; the supplied
nonempty witness set only selects the canonical least value. -/
theorem primeNegOneWitness_le_fixed_squarefree_family {n d s : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hd : 1 < d) (hsf : Squarefree d) (hdec : s ^ 2 * d = n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ s → jacobiSym d p = -1 → fixedSquarefreeCubicBound d < p) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fixedSquarefreeCubicBound d := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_fixed_squarefree_family hn hns hd hsf hdec hGRH hlarge
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- The same fixed-family negative prime also bounds the least non-one
odd-prime witness. Transfer its non-one value and use leastness without
identifying the two least witnesses. -/
theorem primeNeOneWitness_le_fixed_squarefree_family {n d s : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hd : 1 < d) (hsf : Squarefree d) (hdec : s ^ 2 * d = n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ s → jacobiSym d p = -1 → fixedSquarefreeCubicBound d < p) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ fixedSquarefreeCubicBound d := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_fixed_squarefree_family hn hns hd hsf hdec hGRH hlarge
  have hne : jacobiSym n p ≠ 1 := hj.trans_ne (by decide : (-1 : ℤ) ≠ 1)
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

end PseudoPrime.PseudoSquare
