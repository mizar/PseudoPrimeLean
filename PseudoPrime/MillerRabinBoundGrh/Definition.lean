/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic

/-!
# GRH-bound Miller–Rabin witness specification

This module states the target property used by the analytic and algebraic witness construction.
-/

namespace PseudoPrime.MillerRabinBoundGrh

/--
The GRH witness-bound property for every odd composite modulus and every odd-part decomposition
of `n - 1`. A witness is prime, lies below `(log n)^2`, and fails every strong-test acceptance
condition in `ZMod n`.
-/
def PrimeMillerRabinWitnessBound : Prop :=
  AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis →
    ∀ n s d : ℕ,
      1 < n →
      Odd n →
      ¬ Nat.Prime n →
      n - 1 = 2 ^ s * d →
      Odd d →
      ∃ p : ℕ,
        Nat.Prime p ∧
        (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ (1 : ZMod n) ∧
        ∀ j : ℕ, j < s →
          (p : ZMod n) ^ (2 ^ j * d) ≠ (-1 : ZMod n)

end PseudoPrime.MillerRabinBoundGrh
