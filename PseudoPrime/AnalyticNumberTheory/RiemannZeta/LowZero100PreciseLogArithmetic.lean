/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PreciseLogArithmetic

/-! # Precise rational logarithms for the 128 endpoint terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Round the precise Taylor upper endpoint for `log n` to a decimal grid of width `10⁻¹²`.
The argument uses a nearby power of two and 64 Taylor terms. -/
def endpointPreciseLog (n : ℕ) : ℚ :=
  Analysis.rationalGridFloor (10 ^ 12) (Analysis.rationalPreciseLogUpper n (Nat.log2 n + 1) 64)

/-- Check the range of a computed logarithm and its `10⁻¹¹` rational enclosure. The same
check is reused for all critical-line endpoint ordinates. -/
def endpointPreciseLogCheck (n : ℕ) : Bool :=
  decide (0 ≤ endpointPreciseLog n ∧ endpointPreciseLog n ≤ 7) &&
    Analysis.rationalPreciseLogCheck n (Nat.log2 n + 1) 64 (endpointPreciseLog n - 1 / 100000000000)
      (endpointPreciseLog n + 1 / 100000000000)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
