/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.Spec
public import PseudoPrime.PrimeTest.StrongLucas.Prime
public import PseudoPrime.PrimeTest.Selfridge.Candidates
public import PseudoPrime.PrimeTest.Selfridge.Params

/-!
# Selfridge Method A parameters

This module connects the standard Method A choice `P = 1` and
`Q = (1 - D) / 4` to the parameterized Strong Lucas interface.  The search
for an admissible `D` remains a separate executable layer.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Strong Lucas comparison using Method A parameters `P = 1`, `Q = (1 - D) / 4`.
The modulus is natural `n`, and `(1 - D) % 4 = 0` certifies an admissible integer discriminant.
Return the explicit-parameter Strong Lucas Boolean; the congruence proof is not evaluated.
This wrapper separates parameter construction from the search for a suitable `D`.
-/
def strongLucasMethodA (n : ℕ) (D : ℤ) (_hmod : (1 - D) % 4 = 0) : Bool :=
  strongLucasWithParams n D 1 ((1 - D) / 4)

/--
Method A execution agrees with Strong Lucas at the fields of `LucasParams.methodA`.
For any `n`, `D`, and divisibility proof `hmod`, rewrite the constructor's `P` and `Q`
projections; the remaining equality is reflexivity. This bridge exposes the stored
discriminant invariant to the general parameterized prime-completeness theorem.
-/
theorem strongLucasMethodA_eq_parameterized (n : ℕ) (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    strongLucasMethodA n D hmod =
      strongLucasWithParams n D (LucasParams.methodA D hmod).P (LucasParams.methodA D hmod).Q := by
  rw [LucasParams.methodA_P, LucasParams.methodA_Q]
  rfl

/--
A prime `n` passes Method A when `D` is admissible and has Jacobi value `-1` at `n`.
Rewrite Method A to its proof-carrying parameter record and apply Strong Lucas prime
completeness with that record's discriminant equation. Parameter search is a separate
obligation: this theorem assumes the required congruence and Jacobi value.
-/
theorem strongLucasMethodA_of_prime {n : ℕ} (hn : n.Prime) (D : ℤ) (hmod : (1 - D) % 4 = 0)
    (hjacobi : jacobiSym D n = -1) : strongLucasMethodA n D hmod = true := by
  rw [strongLucasMethodA_eq_parameterized]
  exact
    strongLucasWithParams_of_prime hn D (LucasParams.methodA D hmod).P
      (LucasParams.methodA D hmod).Q (LucasParams.methodA D hmod).discr hjacobi

end PseudoPrime.PrimeTest
