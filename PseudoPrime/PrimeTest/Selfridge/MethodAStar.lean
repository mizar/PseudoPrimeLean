/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.Spec
public import PseudoPrime.PrimeTest.StrongLucas.Prime
public import PseudoPrime.PrimeTest.Selfridge.MethodA

/-!
# Selfridge Method A* parameters

Method A* uses `(P,Q) = (5,5)` for `D = 5` and otherwise agrees with Method A.
The admissible `D` search is intentionally kept outside this parameter layer.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Evaluate Strong Lucas with the proof-carrying Method A* parameters at `n` and `D`.
The input congruence permits constructing the parameter record. Use `(5, 5)` at `D = 5`,
and Method A otherwise, then pass all three fields to `strongLucasWithParams`.
The definition chooses parameters only; it does not search for a Jacobi-minus-one discriminant.
-/
def strongLucasMethodAStar (n : ℕ) (D : ℤ) (hmod : (1 - D) % 4 = 0) : Bool :=
  let param := LucasParams.methodAStar D hmod
  strongLucasWithParams n param.D param.P param.Q

/--
Method A* execution is Strong Lucas applied to the fields of its parameter constructor.
This equality holds for every natural `n` and admissible `D` and is proved by reflexivity.
It exposes the record's discriminant equation for parameterized completeness proofs.
-/
theorem strongLucasMethodAStar_eq_parameterized (n : ℕ) (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    strongLucasMethodAStar n D hmod =
      strongLucasWithParams n (LucasParams.methodAStar D hmod).D (LucasParams.methodAStar D hmod).P
        (LucasParams.methodAStar D hmod).Q := by
  rfl

/--
A prime `n` passes Method A* for admissible `D` with Jacobi value `-1`.
The proof shows that either constructor branch preserves `D`, transfers the Jacobi hypothesis,
and applies Strong Lucas prime completeness with the stored discriminant equation.
This supplies the prime-pass contract for Selfridge-based top-level tests after search success.
-/
theorem strongLucasMethodAStar_of_prime {n : ℕ} (hn : n.Prime) (D : ℤ) (hmod : (1 - D) % 4 = 0)
    (hjacobi : jacobiSym D n = -1) : strongLucasMethodAStar n D hmod = true := by
  rw [strongLucasMethodAStar_eq_parameterized]
  let hparam := LucasParams.methodAStar D hmod
  have hD : hparam.D = D := by
    dsimp only [hparam, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi' : jacobiSym hparam.D n = -1 := by simpa only [hD] using hjacobi
  simpa only [hparam] using
    strongLucasWithParams_of_prime hn hparam.D hparam.P hparam.Q hparam.discr hjacobi'

/--
Method A* and Method A have equal Strong Lucas Booleans for every admissible `D ≠ 5`.
Rewrite the complete parameter-record equality and its field projections to obtain the result.
No primality premise is required. Exceptional-discriminant equivalence needs separate identities.
-/
theorem strongLucasMethodAStar_eq_methodA_of_ne_five (n : ℕ) {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hD : D ≠ 5) : strongLucasMethodAStar n D hmod = strongLucasMethodA n D hmod := by
  simp only [strongLucasMethodAStar, strongLucasMethodA,
    LucasParams.methodAStar_eq_methodA_of_ne_five hmod hD]
  rw [LucasParams.methodA_D, LucasParams.methodA_P, LucasParams.methodA_Q]

/--
Symmetric Method A/A* Strong Lucas equality away from `D = 5`.
For arbitrary `n`, admissible `D`, and `D ≠ 5`, reverse the previously proved Method A*-to-A
comparison. This orientation is convenient when rewriting a Method A caller to Method A*.
-/
theorem strongLucasMethodA_eq_methodAStar_of_ne_five (n : ℕ) {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hD : D ≠ 5) : strongLucasMethodA n D hmod = strongLucasMethodAStar n D hmod := by
  exact (strongLucasMethodAStar_eq_methodA_of_ne_five n hmod hD).symm

end PseudoPrime.PrimeTest
