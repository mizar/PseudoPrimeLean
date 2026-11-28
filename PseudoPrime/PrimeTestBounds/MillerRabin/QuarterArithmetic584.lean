/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareGain570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMain570

/-! # Principal and prime-power lower bound on the section 94 interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, three characters trivial at small primes and with trace at least
minus one have total real arithmetic sum above the principal bound with the recovered powers. -/
theorem triple_arithmetic_lower_584 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hl : 288 ≤ r) (hu : r ≤ 292) (hRH : RiemannHypothesis)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    717289 / 1000000 * r - 2403 / 100000 <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  intro X
  have hm := principal_lower_tenth_584 hl hu hRH
  have hw := power_gain_584 a b c (by linarith only [hl]) hu ht hA hB hC
  dsimp only at hm hw
  rw [Complex.re_tsum
      (quarterKernel570.summable_summand (1 : DirichletCharacter ℂ 1)
        (sq_pos_of_pos (by linarith only [hl] : 0 < r)))] at hw
  linarith only [hm, hw]

end PseudoPrime.PrimeTestBounds.MillerRabin
