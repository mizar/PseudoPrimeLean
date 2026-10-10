/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Conjugation of coefficient L-series

Natural complex-power bases identify the conjugate coefficient series with
the reflected original series, including absolute convergence.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For complex coefficients and any complex argument, conjugating a
coefficient L-series term at the reflected argument gives the term with
conjugate coefficients. Natural bases have argument zero, so conjugation
commutes with their complex powers; index zero vanishes.
This identifies the termwise dual Dirichlet series. -/
theorem lSeries_term_star (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun k ↦ star (a k)) s n = star (LSeries.term a (star s) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, star_zero]
  · have harg : (n : ℂ).arg ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_ne_zero.symm
    have hp := Complex.conj_cpow (n : ℂ) s harg
    rw [Complex.conj_natCast] at hp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Complex.star_def, map_div₀]
    rw [← hp]

/-- The L-series with conjugate coefficients at s equals the conjugate
of the original L-series at conjugate s. Conjugation commutes with tsum
and with each natural-base complex-power term. The equality uses totalized
tsum and needs no independent convergence premise.
This represents the arithmetic series of a dual L-function. -/
theorem lSeries_star (a : ℕ → ℂ) (s : ℂ) :
    LSeries (fun n ↦ star (a n)) s = star (LSeries a (star s)) := by
  rw [LSeries, LSeries, tsum_star]
  exact tsum_congr (lSeries_term_star a s)

/-- Absolute convergence of a coefficient L-series at conjugate s gives
absolute convergence of the conjugate-coefficient series at s.
Conjugate the summable terms and use their termwise identity.
This supplies convergence of dual arithmetic sums from the original data. -/
theorem lSeriesSummable_star (a : ℕ → ℂ) (s : ℂ) (hs : LSeriesSummable a (star s)) :
    LSeriesSummable (fun n ↦ star (a n)) s := by
  exact hs.star.congr (fun n ↦ (lSeries_term_star a s n).symm)

end PseudoPrime.NumberTheory
