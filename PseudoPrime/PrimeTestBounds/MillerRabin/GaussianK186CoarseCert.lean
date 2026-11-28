/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import Mathlib.Tactic.FinCases

/-! # Integer checks for the coarse K186 correction moments -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing normalized integer profile is translated once per cell. -/
private def coarseShift (i : ℕ) : MiddleIntRow :=
  baseRow.shift 83 (35 + 6 * (i : ℤ)) 1

/-- Sum the negative coefficients of the requested derivative at width six. -/
private def coarseCoeffSum (row : MiddleIntRow) (j : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 84, max 0 (-(row.num (k + j) * ((k + j).descFactorial j : ℤ))) * 6 ^ k

/-- The integer exponent used to majorize the decaying exponential. -/
private def coarseExponent (i : ℕ) : ℕ :=
  9 * (35 + 6 * i) / 4

/-- Upper bounds on each of the three integrals over the five cells. -/
private def coarseCaps (j i : ℕ) : ℤ :=
  (#[#[376645, 5313082, 39006864, 1784540280, 1425936],
                #[1939665, 23154236, 165659824, 4073577445, 723181],
                #[9673859, 97190201, 678008899, 8785970145, 270622]][j]?.getD
          #[])[i]?.getD
    0

/-- The cap comparison uses only integer products with the common denominator. -/
public def coarseCheck (i : ℕ) : Prop :=
  let row := coarseShift i
  let e := coarseExponent i
  ∀ j : Fin 3, 6 * coarseCoeffSum row j * 10 ^ e ≤ coarseCaps j i * row.den * 27 ^ e

instance (i : ℕ) : Decidable (coarseCheck i) := by
  unfold coarseCheck
  infer_instance

/-- The first cell passes the shared integer check. -/
private theorem coarse_check_0 : coarseCheck 0 := by decide +kernel

/-- The second cell passes the shared integer check. -/
private theorem coarse_check_1 : coarseCheck 1 := by decide +kernel

/-- The third cell passes the shared integer check. -/
private theorem coarse_check_2 : coarseCheck 2 := by decide +kernel

/-- The fourth cell passes the shared integer check. -/
private theorem coarse_check_3 : coarseCheck 3 := by decide +kernel

/-- The fifth cell passes the shared integer check. -/
private theorem coarse_check_4 : coarseCheck 4 := by decide +kernel

/-- Verify one integer shift and three weighted sums for each cell. -/
public theorem coarse_check (i : Fin 5) : coarseCheck i := by
  fin_cases i
  · exact coarse_check_0
  · exact coarse_check_1
  · exact coarse_check_2
  · exact coarse_check_3
  · exact coarse_check_4

end PseudoPrime.PrimeTestBounds.MillerRabin
