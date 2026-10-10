/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import PseudoPrime.NumberTheory.OddNonsquare
public import PseudoPrime.NumberTheory.JacobiWitness.Existence

/-!
# Finite maxima of least Jacobi witnesses

This file defines `QNeOne B` and `QNegOne B`, the largest least odd-prime Jacobi `≠ 1` and `-1`
witnesses on the admissible domain up to `B`. It compares these maxima and lifts a common
nonnegative real pointwise bound to `QNegOne B`. No analytic bound is assumed here.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
The largest least odd-prime Jacobi `≠ 1` witness over the positive odd nonsquares
`n ≤ B` in `admissibleFinset B`. The definition takes `Finset.sup` over the attached
domain, obtaining witness-set nonemptiness from each member's oddness and nonsquareness.
It returns `0` on an empty domain and is used to lift pointwise bounds to uniform maxima.
-/
noncomputable def QNeOne (B : ℕ) : ℕ := by
  classical
    exact
    (NumberTheory.admissibleFinset B).attach.sup fun n =>
      NumberTheory.primeNeOneWitness n.val
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
            ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
            ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare)))

/--
The largest least odd-prime Jacobi `-1` witness over the positive odd nonsquares
`n ≤ B` in `admissibleFinset B`. The definition takes `Finset.sup` over the attached
domain, obtaining witness-set nonemptiness from each member's oddness and nonsquareness.
It returns `0` on an empty domain and is used to lift pointwise bounds to uniform maxima.
-/
noncomputable def QNegOne (B : ℕ) : ℕ := by
  classical
    exact
    (NumberTheory.admissibleFinset B).attach.sup fun n =>
      NumberTheory.primeNegOneWitness n.val
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare))

/--
For `n ∈ admissibleFinset B`, the least odd-prime Jacobi `≠ 1` witness of `n`
is at most `QNeOne B`. The proof unfolds the finite maximum and uses `Finset.le_sup`
for the attached member `⟨n, hn⟩`. This embeds pointwise witnesses into uniform bounds
and supplies lower bounds when an explicit input attains a large witness.
-/
theorem primeNeOneWitness_le_QNeOne {B n : ℕ} (hn : n ∈ NumberTheory.admissibleFinset B) :
    NumberTheory.primeNeOneWitness n
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
            ((NumberTheory.mem_admissibleFinset_iff.mp hn).odd)
            ((NumberTheory.mem_admissibleFinset_iff.mp hn).not_isSquare))) ≤
      QNeOne B := by
  classical
  unfold QNeOne
  simpa only using
    Finset.le_sup (f := fun m : ↥(NumberTheory.admissibleFinset B) =>
      NumberTheory.primeNeOneWitness m.val
        (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
          (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
            ((NumberTheory.mem_admissibleFinset_iff.mp m.property).odd)
            ((NumberTheory.mem_admissibleFinset_iff.mp m.property).not_isSquare))))
      (Finset.mem_attach (NumberTheory.admissibleFinset B) ⟨n, hn⟩)

/--
For every cutoff `B`, `QNeOne B ≤ QNegOne B`: a negative-one witness is also a
non-one witness, so the least non-one witness is no larger at each admissible input.
The proof lifts this pointwise comparison through `Finset.sup_mono_fun`.
This is the comparison component in both finite and analytic maximum bounds.
-/
theorem QNeOne_le_QNegOne (B : ℕ) : QNeOne B ≤ QNegOne B := by
  classical
  unfold QNeOne QNegOne
  apply Finset.sup_mono_fun
  intro n _
  exact
    NumberTheory.primeNeOneWitness_le_primeNegOneWitness n.val
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
        ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
        ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare))

/--
For `n ∈ admissibleFinset B`, the least odd-prime Jacobi `-1` witness of `n`
is at most `QNegOne B`. The proof unfolds the finite maximum and uses `Finset.le_sup`
for the attached member `⟨n, hn⟩`. This embeds pointwise witnesses into uniform bounds
and supplies lower bounds when an explicit input attains a large witness.
-/
theorem primeNegOneWitness_le_QNegOne {B n : ℕ} (hn : n ∈ NumberTheory.admissibleFinset B) :
    NumberTheory.primeNegOneWitness n
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp hn).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp hn).not_isSquare)) ≤
      QNegOne B := by
  classical
  unfold QNegOne
  simpa only using
    Finset.le_sup (f := fun m : ↥(NumberTheory.admissibleFinset B) =>
      NumberTheory.primeNegOneWitness m.val
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp m.property).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp m.property).not_isSquare)))
      (Finset.mem_attach (NumberTheory.admissibleFinset B) ⟨n, hn⟩)

/--
For real `R ≥ 0`, assume every admissible `n ≤ B` has least odd-prime Jacobi `-1`
witness at most `R` after casting to the reals. Then `(QNegOne B : ℝ) ≤ R`.
Supremum induction handles the empty value `0`, binary maxima by `Nat.cast_max`, and
attached members by the supplied bound. This lifts real pointwise estimates to the maximum.
-/
theorem QNegOne_cast_le_of_forall {B : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hbound :
      ∀ n,
        (hn : n ∈ NumberTheory.admissibleFinset B) →
          ((NumberTheory.primeNegOneWitness n
                  (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
                    ((NumberTheory.mem_admissibleFinset_iff.mp hn).odd)
                    ((NumberTheory.mem_admissibleFinset_iff.mp hn).not_isSquare)) :
                ℕ) :
              ℝ) ≤
            R) :
    (QNegOne B : ℝ) ≤ R := by
  classical
  unfold QNegOne
  apply
    Finset.sup_induction (p := fun k : ℕ => (k : ℝ) ≤ R)
      (by
        rw [Nat.bot_eq_zero, Nat.cast_zero]
        exact hR)
  · intro a ha b hb
    simpa only [Nat.cast_max] using max_le ha hb
  · intro n _
    exact hbound n.val n.property

end PseudoPrime.PseudoSquare
