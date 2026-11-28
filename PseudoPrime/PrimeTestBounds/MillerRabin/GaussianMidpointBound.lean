/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMidpointExp
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMidpointExp
import all PseudoPrime.Analysis.RatComplex
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMidpointRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelHeight
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalMoments
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLowZeros
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.Analysis.ExponentialTaylorCertificates
import all PseudoPrime.Analysis.IntegerIntervalHorner
import all PseudoPrime.Analysis.ComputedPhaseRotation
import all PseudoPrime.Analysis.IntegerIntervalComputed

/-! # Kernel-checked midpoint totals for the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- K186 fits the common budget for the 29 midpoint norm enclosures. -/
private theorem midpoint_sum_k186 : highMidpointNormSum .k186 ≤ 856 / 100000 := by decide +kernel

/-- K196 fits the same budget for the 29 midpoint norm enclosures. -/
private theorem midpoint_sum_k196 : highMidpointNormSum .k196 ≤ 856 / 100000 := by decide +kernel

/-- Both midpoint sums are at most 0.00856 by exact integer norm evaluation.
This bound is the midpoint contribution before doubling and adding the bracket and tail errors. -/
public theorem high_midpoint_norm_sum_bound (K : HighGaussianKernel) :
    highMidpointNormSum K ≤ 856 / 100000 := by
  cases K
  · exact midpoint_sum_k186
  · exact midpoint_sum_k196

end PseudoPrime.PrimeTestBounds.MillerRabin
