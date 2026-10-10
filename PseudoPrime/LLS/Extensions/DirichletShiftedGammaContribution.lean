/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.ShiftedGammaContribution
public import PseudoPrime.LLS.Extensions.DirichletSpecialization

/-!
# Degree-one gamma error coefficient

Specialize the integrated gamma-shift bound to the parity shift of a Dirichlet character.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For any complex Dirichlet character and x>1, the real gamma remainder has
form 2*theta/(x*log(x)^2) with |theta|<=1. Its parity shift is zero or one,
so the degree-one specialization needs no RH or primitivity assumption.
This gives the gamma-error scale of the original logarithmic formula. -/
theorem ofDirichletCharacter_gammaLogRemainder_eq_theta {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 < x) :
    ∃ θ : ℝ,
      |θ| ≤ 1 ∧
        ((ofDirichletCharacter χ).gammaLogRemainder x).re = 2 * θ / (x * (Real.log x) ^ 2) := by
  have hκ : ∀ j, 0 ≤ ((ofDirichletCharacter χ).shift j).re := by
    intro j
    change 0 ≤ (if χ (-1) = 1 then (0 : ℂ) else 1).re
    split_ifs <;> norm_num only [Complex.zero_re, Complex.one_re]
  simpa only [ofDirichletCharacter, Nat.cast_one, mul_one] using
    gammaLogRemainder_eq_theta (ofDirichletCharacter χ) hκ hx

end PseudoPrime.LLS.Extensions.GeneralLFunction
