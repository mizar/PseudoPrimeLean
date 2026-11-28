/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSixPoleAbelBound
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSignedPrefix
import Mathlib.Tactic.NormNum

/-! # The Gaussian principal comparison with signed Chebyshev prefix rows -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A compressed radius cell can use the signed Chebyshev rows at its
right endpoint and at the prime-power jumps in its squared interval. -/
public theorem gaussian_principal_box_of_psi_jumps (hRH : RiemannHypothesis) {l y u e H : ℝ}
    (hl : 331 ≤ l) (hly : l ≤ y) (hyu : y ≤ u) (hend : e ≤ Chebyshev.psi (u ^ 2) - u ^ 2)
    (hjump :
      ∀ m : ℕ, IsPrimePow m → (m : ℝ) ∈ Set.Ioc (l ^ 2) (u ^ 2) → e ≤ Chebyshev.psi (m - 1 : ℕ) - m)
    (hH : quarterWeight656 (y ^ 2) 1 ≤ H) :
    let X := y ^ 2
    let w := (quarterKernel656.transform 1).re
    let c := Real.log (2 * Real.pi)
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.71780481 * y + 4 * w * ((if e ≤ 0 then e / l else e / u) + c / u) -
        (100 / 31 - 1.7875 + 3 * c) * H -
        0.026012 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  have hl0 : 0 ≤ l := (by norm_num only : (0 : ℝ) ≤ 331).trans hl
  have hx : y ^ 2 ∈ Set.Icc (l ^ 2) (u ^ 2) :=
    ⟨pow_le_pow_left₀ hl0 hly _, pow_le_pow_left₀ (hl0.trans hly) hyu _⟩
  have he := AnalyticNumberTheory.Arithmetic.psi_signed_floor_of_jumps (sq_nonneg l) hend hjump hx
  exact gaussian_six_pole_principal_box hRH hl hly hyu he hH

end PseudoPrime.PrimeTestBounds.MillerRabin
