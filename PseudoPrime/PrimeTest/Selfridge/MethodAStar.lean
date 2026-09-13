/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.StrongLucas.Spec
import PseudoPrime.PrimeTest.StrongLucas.Prime
import PseudoPrime.PrimeTest.Selfridge.MethodA

/-!
# Selfridge Method A* parameters

Method A* uses `(P,Q) = (5,5)` for `D = 5` and otherwise agrees with Method A.
The admissible `D` search is intentionally kept outside this parameter layer.
-/

namespace PseudoPrime.PrimeTest

/-- Strong Lucas evaluated with the Selfridge Method A* parameters. -/
def strongLucasMethodAStar (n : ℕ) (D : ℤ) (hmod : (1 - D) % 4 = 0) : Bool :=
  let param := LucasParams.methodAStar D hmod
  strongLucasWithParams n param.D param.P param.Q

/-- Method A* evaluates the parameterized Strong Lucas test at its selected parameters. -/
theorem strongLucasMethodAStar_eq_parameterized (n : ℕ) (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    strongLucasMethodAStar n D hmod =
      strongLucasWithParams n (LucasParams.methodAStar D hmod).D (LucasParams.methodAStar D hmod).P
        (LucasParams.methodAStar D hmod).Q := by
  rfl

/-- A prime modulus passes Selfridge Method A* in the Jacobi `-1` branch. -/
theorem strongLucasMethodAStar_of_prime {n : ℕ} (hn : n.Prime) (D : ℤ) (hmod : (1 - D) % 4 = 0)
    (hjacobi : jacobiSym D n = -1) : strongLucasMethodAStar n D hmod = true := by
  rw [strongLucasMethodAStar_eq_parameterized]
  let hparam := LucasParams.methodAStar D hmod
  have hD : hparam.D = D := by
    dsimp [hparam, LucasParams.methodAStar]
    split <;> rfl
  have hjacobi' : jacobiSym hparam.D n = -1 := by simpa only [hD] using hjacobi
  simpa only [hparam] using
    strongLucasWithParams_of_prime hn hparam.D hparam.P hparam.Q hparam.discr hjacobi'

/-- Away from `D = 5`, Method A* and Method A give the same Strong Lucas result. -/
theorem strongLucasMethodAStar_eq_methodA_of_ne_five (n : ℕ) {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hD : D ≠ 5) : strongLucasMethodAStar n D hmod = strongLucasMethodA n D hmod := by
  simp only [strongLucasMethodAStar, strongLucasMethodA,
    LucasParams.methodAStar_eq_methodA_of_ne_five hmod hD]
  rw [LucasParams.methodA_D, LucasParams.methodA_P, LucasParams.methodA_Q]

/-- Away from the exceptional discriminant, the Method A/A* Strong Lucas tests coincide. -/
theorem strongLucasMethodA_eq_methodAStar_of_ne_five (n : ℕ) {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hD : D ≠ 5) : strongLucasMethodA n D hmod = strongLucasMethodAStar n D hmod := by
  exact (strongLucasMethodAStar_eq_methodA_of_ne_five n hmod hD).symm

end PseudoPrime.PrimeTest
