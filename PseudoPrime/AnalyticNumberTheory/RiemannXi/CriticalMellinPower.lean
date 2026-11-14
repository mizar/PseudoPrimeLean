/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinTerm
public import PseudoPrime.Analysis.PreciseLogTaylorBounds

/-! # Rational grid powers for critical-line certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The binary scale of the sixteenth-grid node indexed by `i`. The six
cases normalize the node for the rational logarithm computation. -/
def certificateBinaryScale (i : ℕ) : ℕ :=
  if i ≤ 16 then 1
  else if i ≤ 48 then 2 else if i ≤ 112 then 3 else if i ≤ 240 then 4 else if i ≤ 496 then 5 else 6

/-- The lower rational logarithm approximation for a node and binary scale.
It combines a fixed enclosure of `log 2`, a Taylor sum, and its remainder. -/
def certificateLogLower (N : ℚ) (j : ℕ) : ℚ :=
  j * (693147180559945309417232121458176568075500134360255254120680 / 10 ^ 60) -
    Analysis.rationalLogSeries (1 - N / 2 ^ j) 256 -
    Analysis.rationalLogRemainder (1 - N / 2 ^ j) 256

/-- The upper rational logarithm approximation for a node and binary scale.
It uses the same Taylor sum and the opposite sign for the remainder. -/
def certificateLogUpper (N : ℚ) (j : ℕ) : ℚ :=
  j * (693147180559945309417232121458176568075500134360255254120681 / 10 ^ 60) -
      Analysis.rationalLogSeries (1 - N / 2 ^ j) 256 +
    Analysis.rationalLogRemainder (1 - N / 2 ^ j) 256

/-- The fixed-grid rational logarithm midpoint, rounded downward to a grid
of denominator `10^55`, for use in the power certificate. -/
def certificateLogRounded (i : ℕ) : ℚ :=
  let N : ℚ := 1 + (i : ℚ) / 16
  let j := certificateBinaryScale i
  Analysis.rationalGridFloor (10 ^ 55) ((certificateLogLower N j + certificateLogUpper N j) / 2)

/-- The rational amplitude and phase approximation at a grid node and
rational height. Its output is a component pair for cell certificates. -/
def certificateGridPower (i : ℕ) (t : ℚ) : ℚ × ℚ :=
  let c := certificateLogRounded i
  let q : ℚ := -(3 / 4) * c
  let a : ℚ := ∑ k ∈ Finset.range 64, q ^ k / (k.factorial : ℚ)
  let z := Analysis.rationalScaledPhase (10 ^ 60) (c * t / 2) 64 8
  (a * z.1, a * z.2)

end PseudoPrime.AnalyticNumberTheory.RiemannXi
