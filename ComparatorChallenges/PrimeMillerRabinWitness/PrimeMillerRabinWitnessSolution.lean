/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.GRH.EquivalentForms
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsBridge
import PseudoPrime.PrimeTestBounds.MillerRabin.LogNineBridge
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCriterionTo663
import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian027007
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Comparator solution: reproduce the challenge statements and use the library proof. -/

@[expose] public section

namespace ComparatorChallenges.PrimeMillerRabinWitness

/-- The open-critical-strip formulation of the generalized Riemann hypothesis
for Dirichlet L-functions. For every nonzero modulus `N` and every Dirichlet
character `χ` modulo `N`, any zero of `χ.LFunction` with `0 < s.re < 1` has
real part `1 / 2`. This formulation supports specialization to modulus one. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- The open-critical-strip hypothesis for Dirichlet L-functions implies the
Riemann hypothesis. The classification of zeta zeros with `s.re ≤ 0` and
nonvanishing for `1 ≤ s.re` put every nontrivial zeta zero in the open strip.
The Dirichlet L-function for the character modulo one equals `riemannZeta`,
so the hypothesis places each such zero on the critical line. -/
theorem DirichletLZerosOnLine.riemann (h : DirichletLZerosOnLine) : RiemannHypothesis := by
  intro s hz ht _
  exact
    h 1 1 s (lt_of_not_ge fun hs ↦ ht ((riemannZeta_eq_zero_iff_of_re_nonpos hs).mp hz))
      (lt_of_not_ge fun hs ↦ riemannZeta_ne_zero_of_one_le_re hs hz)
      (DirichletCharacter.LFunction_modOne_eq.symm ▸ hz)

/-- The strong Miller–Rabin probable-prime condition for a natural input `n` and base `a`.
With `(s, d) = Nat.maxPowDvdDiv 2 (n - 1)`, it asserts that `a^d = 1` in `ZMod n`, or that
`a^(2^j * d) = -1` for some `j < s`. The proposition is defined for all natural inputs and
expresses the base test used by the prime-base criteria below. -/
def IsStrongMillerRabinProbablePrime (n a : ℕ) : Prop :=
  let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
  (a : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (a : ZMod n) ^ (2 ^ j * d) = -1

/-- Under GRH, an odd natural number `n > 1` is prime if and only if it passes the strong
Miller–Rabin test for every prime base at most `2 * (logb 9 n)^2`. This states the challenge
for the base-nine logarithmic cutoff; its proof is supplied by the comparator solution. -/
theorem prime_millerRabin_log_nine_criterion (hG : DirichletLZerosOnLine) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (2 * ((Real.logb 9 n) ^ 2)) → IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  have hGRH := PseudoPrime.AnalyticNumberTheory.GRH.zeros_on_line_iff_grh.mp hG
  exact PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_log_nine_criterion hGRH hn ho

/-- Under GRH, an odd natural number `n > 1` is prime if and only if it passes
the strong Miller–Rabin test for every prime base at most
`max 2 ((3 / 11) * (log n)^2)`. The composite direction uses the least
rejecting-prime bound, and the prime direction uses base-two acceptance and
the log-square bound. -/
theorem prime_millerRabin_027273_criterion (hG : DirichletLZerosOnLine) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (max 2 ((3 / 11 : ℝ) * ((Real.log n) ^ 2))) →
          IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  have hGRH := PseudoPrime.AnalyticNumberTheory.GRH.zeros_on_line_iff_grh.mp hG
  exact PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_027_criterion hGRH hn ho

/-- Assume GRH in the form `DirichletLZerosOnLine`. An odd natural number
`n > 1` is prime exactly when it passes the strong Miller–Rabin test for every
prime base at most `max 2 (max (L^2 / 4) ((9090 / 33659) * L^2 -
(53 / 4) * L * exp (-(L / 11000)^2)))`, where `L = log n`.
The library proof joins the uniform Korselt triple ranges before combining
them with the nonuniform and small-input bounds. -/
theorem prime_millerRabin_027007_gaussian_criterion (hG : DirichletLZerosOnLine) {n : ℕ}
    (hn : 1 < n) (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤
            (max 2
              (max ((1 / 4 : ℝ) * ((Real.log n) ^ 2))
                ((9090 / 33659 : ℝ) * ((Real.log n) ^ 2) -
                  (53 / 4 : ℝ) * (Real.log n) * (Real.exp (-((Real.log n) / 11000) ^ 2))))) →
          IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  have hGRH := PseudoPrime.AnalyticNumberTheory.GRH.zeros_on_line_iff_grh.mp hG
  exact
    PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_027007_gaussian_criterion hGRH hn ho

/-- Assume GRH in the form `DirichletLZerosOnLine`. An odd natural number
`n > 1` is prime exactly when it passes the strong Miller–Rabin test for every
prime base at most `max 2 ((9090 / 33659) * (log n)^2)`.
The proof uses the Gaussian criterion and bounds its cutoff by this
quadratic expression. -/
theorem prime_millerRabin_027007_criterion (hG : DirichletLZerosOnLine) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (max 2 ((9090 / 33659 : ℝ) * ((Real.log n) ^ 2))) →
          IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  have hGRH := PseudoPrime.AnalyticNumberTheory.GRH.zeros_on_line_iff_grh.mp hG
  exact PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_027007_criterion hGRH hn ho

/-- Under GRH, an odd natural number `n > 1` with `log n ≤ 663` is prime
if and only if it passes the strong Miller–Rabin test for every prime base
at most `max 2 ((1 / 4) * (log n)^2)`. -/
theorem prime_millerRabin_025_L663_criterion (hG : DirichletLZerosOnLine) {n : ℕ} (hn : 1 < n)
    (hln : (Real.log n) ≤ 663) (ho : Odd n) :
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ (max 2 ((1 / 4 : ℝ) * ((Real.log n) ^ 2))) →
          IsStrongMillerRabinProbablePrime n p) ↔
      Nat.Prime n := by
  have hGRH := PseudoPrime.AnalyticNumberTheory.GRH.zeros_on_line_iff_grh.mp hG
  exact PseudoPrime.PrimeTestBounds.MillerRabin.prime_millerRabin_025_L663_criterion hGRH hn hln ho

end ComparatorChallenges.PrimeMillerRabinWitness
