/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.ReferenceArithmetic
import PseudoPrime.NumberTheory.Fibonacci.Euclid
import Mathlib.Data.Nat.PadicValNat

/-! # Batched Jacobi procedures with certified Fibonacci fuel bounds

The fuel counts odd-part extraction followed by reciprocity and remainder updates.
Zero termination is free; maximal-power extraction uses mathlib's two-adic operations.
-/

namespace PseudoPrime.PrimeTest.ReferenceArithmetic

/--
For a nonzero numerator, one batched round preserves the batched reference value.
Unfold the recursive reference procedure at its nonzero branch. The returned odd-part
remainder and sign are exactly the step used by the fuel-bounded implementation.
-/
theorem jacobiNat_round (a n : ℕ) (ha : a ≠ 0) :
    jacobiNat a n =
      jacobiRoundSign a n * jacobiNat (n % Nat.divMaxPow a 2) (Nat.divMaxPow a 2) := by
  rw [jacobiNat, dite_eq_right ha]

/--
Fuel-bounded Jacobi procedure on natural numerator `a` and modulus `n`.
Each positive-numerator round removes all factors of two using `padicValNat` and
`Nat.divMaxPow`, updates the sign, and recurses on the remainder with one less fuel.
A zero numerator terminates without spending fuel, returning one only at modulus one.
A nonzero numerator with zero fuel returns `none`, distinct from the Jacobi value zero.
Agreement with `jacobiSym` requires an odd modulus; termination bounds do not.
-/
def jacobiNatBatchedFuel : ℕ → ℕ → ℕ → Option ℤ
  | 0, a, n => if a = 0 then some (if n = 1 then 1 else 0) else none
  | fuel + 1, a, n =>
    if a = 0 then some (if n = 1 then 1 else 0)
    else
      (jacobiNatBatchedFuel fuel (n % Nat.divMaxPow a 2) (Nat.divMaxPow a 2)).map
        (jacobiRoundSign a n * ·)

/--
Exhaustion of the batched procedure yields a nonterminal divisor-reducing trajectory.
Induction on fuel chooses the positive odd part at each round. No parity assumption
on the original modulus is needed for this termination statement.
-/
theorem jacobiNatBatchedFuel_none_nonstop (fuel a n : ℕ)
    (h : jacobiNatBatchedFuel fuel a n = none) :
    PseudoPrime.NumberTheory.Euclid.divisionNonstop fuel n a := by
  induction fuel generalizing a n with
  | zero =>
    by_cases ha : a = 0
    · simp only [jacobiNatBatchedFuel, ha, ↓reduceIte, Option.some_ne_none] at h
    · exact ha
  | succ fuel ih =>
    by_cases ha : a = 0
    · simp only [jacobiNatBatchedFuel, ha, ↓reduceIte, Option.some_ne_none] at h
    · rw [jacobiNatBatchedFuel, ite_eq_right ha, Option.map_eq_none_iff] at h
      exact ⟨Nat.divMaxPow a 2, oddPart_pos a ha, oddPart_le a ha, ih _ _ h⟩

/--
For an odd modulus and any caller budget, the result is either exhaustion or the reference value.
Induction on fuel preserves both possibilities through the batched sign update.
An insufficient budget never produces an incorrect successful result.
-/
theorem jacobiNatBatchedFuel_result (fuel a n : ℕ) (hn : n % 2 = 1) :
    jacobiNatBatchedFuel fuel a n = none ∨
      jacobiNatBatchedFuel fuel a n = some (jacobiNat a n) := by
  induction fuel generalizing a n with
  | zero =>
    by_cases ha : a = 0
    · right
      subst a
      rw [jacobiNatBatchedFuel, jacobiNat]
      simp only [↓reduceIte, ↓reduceDIte]
    · left
      exact ite_eq_right ha
  | succ fuel ih =>
    by_cases ha : a = 0
    · right
      subst a
      rw [jacobiNatBatchedFuel, jacobiNat]
      simp only [↓reduceIte, ↓reduceDIte]
    · rcases ih (n % Nat.divMaxPow a 2) (Nat.divMaxPow a 2) (oddPart_odd a ha) with h | h
      · left
        rw [jacobiNatBatchedFuel, ite_eq_right ha, h, Option.map_none]
      · right
        rw [jacobiNatBatchedFuel, ite_eq_right ha, h, Option.map_some, jacobiNat_round a n ha]

/--
With an odd modulus and no nonterminal divisor trajectory of the given length,
the batched procedure returns the reference Jacobi value. The result dichotomy leaves
only exhaustion to exclude; its extracted trajectory contradicts the hypothesis.
-/
theorem jacobiNatBatchedFuel_complete (fuel a n : ℕ) (hn : n % 2 = 1)
    (hb : ¬PseudoPrime.NumberTheory.Euclid.divisionNonstop fuel n a) :
    jacobiNatBatchedFuel fuel a n = some (jacobiNat a n) := by
  rcases jacobiNatBatchedFuel_result fuel a n hn with h | h
  · exact False.elim (hb (jacobiNatBatchedFuel_none_nonstop _ _ _ h))
  · exact h

/--
For an odd modulus, every fuel budget at least `stepBound a` returns the reference value.
The Fibonacci threshold rules out a nonterminal trajectory. This connects the general
Euclidean bound to the actual batched Jacobi implementation.
-/
theorem jacobiNatBatchedFuel_eq (fuel a n : ℕ) (hn : n % 2 = 1)
    (hf : PseudoPrime.NumberTheory.Euclid.stepBound a ≤ fuel) :
    jacobiNatBatchedFuel fuel a n = some (jacobiNat a n) := by
  apply jacobiNatBatchedFuel_complete fuel a n hn
  apply PseudoPrime.NumberTheory.Euclid.not_divisionNonstop_of_lt_fib
  exact
    (PseudoPrime.NumberTheory.Euclid.lt_fib_stepBound a).trans_le
      (Nat.fib_mono (Nat.add_le_add_right hf 2))

/--
Natural-numerator batched Jacobi entry point using the fast Fibonacci budget `stepBound a`.
It extracts the result of the fuel-bounded procedure, with zero as the fallback.
For odd moduli the sufficient-fuel theorem proves that this fallback is unreachable.
-/
def jacobiNatBatched (a n : ℕ) : ℤ :=
  (jacobiNatBatchedFuel (PseudoPrime.NumberTheory.Euclid.stepBound a) a n).getD 0

/--
For an odd modulus, the automatically budgeted batched entry point equals `jacobiNat`.
The sufficient-fuel theorem eliminates exhaustion and identifies the returned value.
-/
theorem jacobiNatBatched_eq (a n : ℕ) (hn : n % 2 = 1) : jacobiNatBatched a n = jacobiNat a n := by
  rw [jacobiNatBatched, jacobiNatBatchedFuel_eq _ _ _ hn le_rfl, Option.getD_some]

/--
Signed batched Jacobi entry point using the absolute numerator and its Fibonacci budget.
A negative numerator contributes the modulus-four sign. For odd moduli the result is
the ordinary Jacobi symbol, including genuine zero values.
-/
def jacobiSignedBatched (a : ℤ) (n : ℕ) : ℤ :=
  (if a < 0 ∧ n % 4 = 3 then -1 else 1) * jacobiNatBatched a.natAbs n

/--
For every integer numerator and odd modulus, the signed batched entry equals `jacobiSym`.
Replace its natural entry by the reference recursion and apply the signed reference theorem.
-/
theorem jacobiSignedBatched_eq (a : ℤ) (n : ℕ) (hn : n % 2 = 1) :
    jacobiSignedBatched a n = jacobiSym a n := by
  rw [jacobiSignedBatched, jacobiNatBatched_eq _ _ hn]
  exact jacobiSigned_eq a n hn

/--
Batched Jacobi entry after Euclidean remainder normalization of an integer numerator.
The nonnegative remainder is converted to a natural and given its own Fibonacci budget.
For positive odd moduli this preserves the symbol and bounds the input by the modulus.
-/
def jacobiNormalizedBatched (a : ℤ) (n : ℕ) : ℤ :=
  jacobiNatBatched (a % (n : ℤ)).toNat n

/--
For every integer numerator and odd modulus, the normalized batched entry equals `jacobiSym`.
Nonnegativity justifies the natural conversion; remainder invariance identifies the result.
-/
theorem jacobiNormalizedBatched_eq (a : ℤ) (n : ℕ) (hn : n % 2 = 1) :
    jacobiNormalizedBatched a n = jacobiSym a n := by
  have hp : 0 < n :=
    Nat.pos_of_ne_zero
      (fun h ↦ by
        subst n; contradiction)
  have hr := Int.emod_nonneg a (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hp))
  rw [jacobiNormalizedBatched, jacobiNatBatched_eq _ _ hn, jacobiNat_eq _ _ hn,
    Int.toNat_of_nonneg hr, ← jacobiSym.mod_left]

/--
For an odd modulus, `2 * log2 (a + 1) + 1` rounds suffice for a natural numerator.
This integer-logarithm corollary bounds the fast Fibonacci budget from above.
-/
theorem jacobiNatBatchedFuel_log2 (a n : ℕ) (hn : n % 2 = 1) :
    jacobiNatBatchedFuel (2 * (a + 1).log2 + 1) a n = some (jacobiSym (a : ℤ) n) := by
  rw [jacobiNatBatchedFuel_eq _ _ _ hn (PseudoPrime.NumberTheory.Euclid.stepBound_le_log2 a),
    jacobiNat_eq _ _ hn]

/--
Every budget at least `stepBound a` prevents exhaustion, for all natural moduli.
The trajectory extracted from `none` contradicts the Fibonacci nontermination threshold.
Semantic correctness is separately stated for odd moduli.
-/
theorem jacobiNatBatchedFuel_ne_none (fuel a n : ℕ)
    (hf : PseudoPrime.NumberTheory.Euclid.stepBound a ≤ fuel) :
    jacobiNatBatchedFuel fuel a n ≠ none := by
  intro h
  exact
    PseudoPrime.NumberTheory.Euclid.not_divisionNonstop_of_lt_fib n a fuel
      ((PseudoPrime.NumberTheory.Euclid.lt_fib_stepBound a).trans_le
        (Nat.fib_mono (Nat.add_le_add_right hf 2)))
      (jacobiNatBatchedFuel_none_nonstop _ _ _ h)

/--
Increasing the numerator cannot decrease the Fibonacci fuel budget.
Monotonicity of the greatest Fibonacci index survives natural subtraction by one.
This transfers an input-specific budget to a uniform modulus-dependent budget.
-/
theorem jacobiStepBound_mono {a b : ℕ} (h : a ≤ b) :
    PseudoPrime.NumberTheory.Euclid.stepBound a ≤ PseudoPrime.NumberTheory.Euclid.stepBound b := by
  rw [PseudoPrime.NumberTheory.Euclid.stepBound_eq, PseudoPrime.NumberTheory.Euclid.stepBound_eq]
  exact Nat.sub_le_sub_right (Nat.greatestFib_mono h) 1

/--
For a positive modulus, the normalized integer numerator is strictly below that modulus.
The Euclidean remainder bounds and its nonnegativity justify conversion to a natural.
-/
theorem jacobiNormalized_lt (a : ℤ) (n : ℕ) (hn : 0 < n) : (a % (n : ℤ)).toNat < n := by
  exact
    (Int.toNat_lt (Int.emod_nonneg a (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn)))).mpr
      (Int.emod_lt_of_pos a (Int.natCast_pos.mpr hn))

/--
For an integer numerator and odd modulus, `stepBound (n - 1)` is a uniform sufficient budget
after remainder normalization. Monotonicity transfers the remainder bound to this budget;
reference correctness and remainder invariance identify the returned Jacobi symbol.
-/
theorem jacobiNormalizedBatchedFuel_eq (a : ℤ) (n fuel : ℕ) (hn : n % 2 = 1)
    (hf : PseudoPrime.NumberTheory.Euclid.stepBound (n - 1) ≤ fuel) :
    jacobiNatBatchedFuel fuel (a % (n : ℤ)).toNat n = some (jacobiSym a n) := by
  have hp : 0 < n :=
    Nat.pos_of_ne_zero
      (fun h ↦ by
        subst n; contradiction)
  have hb := jacobiStepBound_mono (Nat.le_pred_of_lt (jacobiNormalized_lt a n hp))
  rw [jacobiNatBatchedFuel_eq _ _ _ hn (hb.trans hf), jacobiNat_eq _ _ hn,
    Int.toNat_of_nonneg (Int.emod_nonneg a (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hp))), ←
    jacobiSym.mod_left]

/--
For an integer numerator and odd modulus, `2 * log2 n + 1` rounds suffice after normalization.
Apply the uniform Fibonacci budget and its integer-logarithm upper bound.
-/
theorem jacobiNormalizedBatchedFuel_log2 (a : ℤ) (n : ℕ) (hn : n % 2 = 1) :
    jacobiNatBatchedFuel (2 * n.log2 + 1) (a % (n : ℤ)).toNat n = some (jacobiSym a n) := by
  apply jacobiNormalizedBatchedFuel_eq a n _ hn
  have hp : 0 < n :=
    Nat.pos_of_ne_zero
      (fun h ↦ by
        subst n; contradiction)
  simpa only [Nat.sub_add_cancel hp] using PseudoPrime.NumberTheory.Euclid.stepBound_le_log2 (n - 1)

/--
For an odd modulus, every successful result equals `jacobiSym`, without a fuel lower bound.
The result dichotomy excludes exhaustion and identifies the returned integer.
-/
theorem jacobiNatBatchedFuel_sound {fuel a n : ℕ} {z : ℤ} (hn : n % 2 = 1)
    (h : jacobiNatBatchedFuel fuel a n = some z) : z = jacobiSym (a : ℤ) n := by
  rcases jacobiNatBatchedFuel_result fuel a n hn with hz | hz
  · rw [h] at hz
    cases hz
  · rw [h] at hz
    exact (Option.some.inj hz).trans (jacobiNat_eq a n hn)

/-- Executable Jacobi entry on every integer numerator and natural modulus.
Odd moduli use remainder normalization and certified batched Fibonacci fuel.
Other moduli use the existing convention of jacobiSym, preserving the all-input contract.
This entry supplies executable guards while their proofs continue to use jacobiSym. -/
def jacobiExecutable (a : ℤ) (n : ℕ) : ℤ :=
  if n % 2 = 1 then jacobiNormalizedBatched a n else jacobiSym a n

/-- The executable entry agrees with jacobiSym on all inputs.
The odd branch uses certified batched correctness; the other branch is unchanged.
This equality transfers existing stopping predicates and proof-carrying classifications. -/
theorem jacobiExecutable_eq (a : ℤ) (n : ℕ) : jacobiExecutable a n = jacobiSym a n := by
  unfold jacobiExecutable
  split
  · next hn => exact jacobiNormalizedBatched_eq a n hn
  · rfl

/-- Decide a mathematical Jacobi equality using the certified executable entry.
The returned true or false evidence is transported through jacobiExecutable_eq.
This lets dependent consumers retain their existing jacobiSym hypotheses. -/
def jacobiEqDecidable (a : ℤ) (n : ℕ) (z : ℤ) : Decidable (jacobiSym a n = z) :=
  if hj : jacobiExecutable a n = z then isTrue ((jacobiExecutable_eq a n).symm.trans hj)
  else isFalse (fun h ↦ hj ((jacobiExecutable_eq a n).trans h))

/-- The executable equality decision agrees with the existing decision on all inputs.
Subsingleton uniqueness identifies both decisions and their proof evidence.
This equality preserves dependent classifications while changing their computation. -/
theorem jacobiEqDecidable_eq (a : ℤ) (n : ℕ) (z : ℤ) :
    jacobiEqDecidable a n z = (inferInstance : Decidable (jacobiSym a n = z)) := by
  exact Subsingleton.elim _ _

end PseudoPrime.PrimeTest.ReferenceArithmetic
