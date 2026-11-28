/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH

/-! # Certified low zero ordinates for quarter-kernel phase sums -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the same ordered list of 29 positive zeta ordinates is enclosed
by the certified brackets, exhausts the positive zeros through height 100,
and has multiplicity one at each index. The count theorem upgrades the
bracketed existence theorem without changing its witness. -/
theorem quarter_low_zeros_complete (hRH : RiemannHypothesis) :
    ∃ g : Fin 29 → ℝ,
      StrictMono g ∧
        (∀ i, 0 < g i) ∧
        (∀ i, g i ≤ 100) ∧
        (∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0) ∧
        AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g ∧
        AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g ∧
        ((AnalyticNumberTheory.RiemannZeta.zerosUpTo 100).filter (fun ρ ↦ 0 < ρ.im)) ⊆
          Finset.univ.image (fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) ∧
        ∀ i,
          AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity
              (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) =
            1 := by
  obtain ⟨g, hm, hp, hh, hz, hl, hu⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  have hc := (AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH).le
  have h := AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH hc g hm hp hh hz
  exact ⟨g, hm, hp, hh, hz, hl, hu, h.1, h.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
