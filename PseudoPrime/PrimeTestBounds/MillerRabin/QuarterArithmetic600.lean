/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterOdd574

/-! # Arithmetic comparison for section 99 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The principal bound and the recovered prime powers give the arithmetic
lower bound for the section 99 triple under RH. -/
theorem section99_arithmetic_of_RH {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    let X := r ^ 2
    0.717289 * r - 0.29136 - 0.0273 + (if r ≤ 299 then 0.002237 else 0.002229) -
          3 * Real.log (2 * Real.pi) * quarterWeight570 X 1 +
        0.09239 +
        (if r ≤ 299 then 0.01154 else 0.01232) <
      (∑' k : ℕ, quarterKernel570.summand a X k).re +
        (∑' k : ℕ, quarterKernel570.summand b X k).re +
        (∑' k : ℕ, quarterKernel570.summand c X k).re := by
  apply section99_arithmetic_recovered a b c hl hu ht hA hB hC
  dsimp only
  have hx : 0 < r ^ 2 := sq_pos_of_pos (by linarith only [hl])
  rw [Complex.re_tsum (quarterKernel570.summable_summand (1 : DirichletCharacter ℂ 1) hx)]
  exact (section99_principal_lower_RH hRH hl hu).le

end PseudoPrime.PrimeTestBounds.MillerRabin
