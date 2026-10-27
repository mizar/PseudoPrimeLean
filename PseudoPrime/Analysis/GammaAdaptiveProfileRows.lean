/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicAnchorBounds

/-! # Scale-parametric cells and adaptive prime-row factories -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a rational scale s, root multipliers and logarithmic endpoints.
Definition: lo=s*a^2, hi=s*b^2, rootLo=rlo*a, rootHi=rhi*b and theta=5/4.
Output: local cell data requiring a separate validity check.
Role: allow the kernel scale to vary when comparing coefficient one with smaller coefficients. -/
def gammaScaledEnvelopeCell (s rlo rhi a b : ℚ) : GammaLocalCellData :=
  { lo := s * a ^ 2, hi := s * b ^ 2, rootLo := rlo * a, rootHi := rhi * b, theta := 5 / 4 }

/-- Input: any checked local cell and a prime candidate.
Definition: reuse the logarithm and ramp data, replacing Euler, cost and excess allowances
by the adaptive anchor bounds and outer rounding. Output: a compact computed row.
Role: reuse the same local-row checker for arbitrary kernel scales. -/
def gammaAdaptiveProfileRow (c : GammaLocalCellData) (p : ℕ) : GammaLocalPrimeRow :=
  let r := gammaProfileEnvelopeRow c p
  let E := gammaAdaptiveEulerUpper p
  let C := gammaCellGridCeil (E + max r.rampUpper 0 / c.rootLo)
  { r with
    eulerUpper := E
    costUpper := C
    excessUpper := gammaCellGridCeil (max (C - c.theta / c.rootHi) 0) }

end PseudoPrime.Analysis
