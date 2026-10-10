/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.CharacterBound
public import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum
public import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq
public import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaEnvelope
public import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal
public import PseudoPrime.PseudoSquare.Bounds.PointwiseWitness
public import PseudoPrime.PseudoSquare.Computation.SmallN
public import PseudoPrime.PseudoSquare.Computation.QThresholds
public import PseudoPrime.PseudoSquare.Computation.QNeOneFiniteLogSq
public import PseudoPrime.PseudoSquare.Computation.SmallNegOne.Below399

/-!
# PseudoSquare umbrella module

This module is the public import boundary for the `PseudoSquare` development.
It assembles applications of the general quadratic-character and LLS layers to
Jacobi witnesses, their maxima, explicit GRH bounds, and computational certificates.

The imports are intentionally kept here as an umbrella rather than duplicated
in the package root. Computational certificates and analytic theorems remain
in their focused submodules, where they can be built and checked independently.
General foundations have their own `PseudoPrime.Analysis`,
`PseudoPrime.AnalyticNumberTheory`, and `PseudoPrime.NumberTheory` umbrellas.
Executable primality tests and Selfridge bounds are exposed by
`PseudoPrime.PrimeTest` and `PseudoPrime.PrimeTestBounds.Selfridge`, respectively.
-/

@[expose] public section
