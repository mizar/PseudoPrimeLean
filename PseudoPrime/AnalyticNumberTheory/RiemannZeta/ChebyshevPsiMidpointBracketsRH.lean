/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMidpointBudget100RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadDistance100
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets

/-! # ψ midpoint budget from ordered low-zero brackets -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, 29 ordered positive zeros in the stated brackets and a height-100
count of at most 58 supply the zero count and the distance bound needed for
the midpoint ψ estimate. The two signed midpoint sums remain explicit. -/
theorem psi_error_midpoint_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D C : ℝ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((x - h + x) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C)
    (hhi :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((x + (x + h)) / 2) : ℂ) ^ ρ / ρ)).re| ≤
        C) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) + (C + 3640 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  have h100 := (head100_of_count hRH g hmono hpos hheight hzero hcount hl).1
  have hm := (zero_head_distance100_lt hRH g hmono hpos hheight hzero hcount hu).le
  exact psi_error_midpoint_budget100 hRH h100 hT hh hx hD hsqrt htail hm hlo hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
