/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegralMain194
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLeeNosalMillion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # The first two intervals of the normalized ψ envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `[101, 1423)`, the normalized ψ error is at most the Lee–Nosal
logarithmic envelope. This follows unconditionally from the finite certificate. -/
theorem psi_normalized_101_1423 {x : ℝ} (ha : 101 ≤ x) (hb : x < 1423) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ leeNosalPsiLog (Real.log x) := by
  have hx : 0 < x := by linarith only [ha]
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  apply (div_le_iff₀ hs).2
  have h := psi_lee_nosal_101_million ha (show x ≤ 1000000 by linarith only [hb])
  dsimp only [leeNosalPsiLog]
  linarith only [h]

/-- On `[1423, 1000000]`, the normalized ψ error is at most 4/5. This is the
unconditional finite square-root certificate expressed as a quotient. -/
theorem psi_normalized_1423_million {x : ℝ} (ha : 1423 ≤ x) (hb : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  exact Arithmetic.psi_four_fifths_1423_million ha hb

/-- The requested piecewise normalized bound holds unconditionally from 101
through one million. The branch point is 1423, and the finite certificates
are used through their table-free theorems. -/
theorem psi_normalized_piecewise_million {x : ℝ} (ha : 101 ≤ x) (hb : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      if x < 1423 then leeNosalPsiLog (Real.log x) else 4 / 5 := by
  split_ifs with h
  · exact psi_normalized_101_1423 ha h
  · exact psi_normalized_1423_million (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
