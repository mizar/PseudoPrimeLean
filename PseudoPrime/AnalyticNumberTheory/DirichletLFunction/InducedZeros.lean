/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Nonvanishing of Euler factors for changed-level Dirichlet L-functions

These results are independent of the project's quadratic character construction. The final
specialization from a quadratic character to its primitive character remains in
`JacobiCharacterInducedZeros`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- An Euler factor of a Dirichlet L-function is nonzero when the real part is positive. -/
theorem eulerFactor_ne_zero_in_rightHalfPlane {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) : 1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  rw [sub_ne_zero]
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    exact
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
        (by
          rw [Complex.neg_re]
          linarith only [hs])
  have hnorm : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_right (χ.norm_le_one p) (norm_nonneg _)).trans_lt
        (by simpa only [one_mul] using hpow)
  exact fun h => by
    rw [← h, norm_one] at hnorm
    exact (lt_irrefl 1 hnorm)

/-- The finite product of Euler factors introduced at a larger level is nonzero. -/
theorem eulerFactorProduct_ne_zero_in_rightHalfPlane {M N : ℕ} (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 0 < s.re) : ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact
    eulerFactor_ne_zero_in_rightHalfPlane χ
      (Nat.prime_of_mem_primeFactors hp) hs

/-- A zero in the right half-plane of a changed-level character is a zero before changing level. -/
theorem changeLevel_zero_of_rightHalfPlane {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) {s : ℂ}
    (hszero : (DirichletCharacter.changeLevel hMN χ).LFunction s = 0) (hs : 0 < s.re) :
    χ.LFunction s = 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inl hχ)] at hszero
  exact
    (mul_eq_zero.mp hszero).resolve_right
      (eulerFactorProduct_ne_zero_in_rightHalfPlane
        χ hs)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
