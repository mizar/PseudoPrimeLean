/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.PrimeSums.Mertens
public import PseudoPrime.LLS.Extensions.GeneralValueVariants

/-!
# General L-value variants with discharged arithmetic inputs

The unconditional second-order psi theorem supplies the Mangoldt-Mertens estimate
and both corrected general L-value variants. Their internal general L-function
hypotheses remain those of the existing specifications.
-/

public section

namespace PseudoPrime.LLS

/-- The degree-at-least-two general L-value variant holds with its original internal
admissibility and individual-function RH assumptions. Supply the unconditional
arithmetic psi input to the existing criterion. No extra zeta RH or unproved
Mangoldt estimate is added to the statement. -/
theorem generalL_ge_two_proof : Extensions.lls_generalL_ge_two := by
  exact
    Extensions.GeneralLFunction.generalL_ge_two_of_psi
      AnalyticNumberTheory.PrimeSums.psiSecondOrderBound_unconditional

/-- The nonvanishing error-scale general L-value variant holds with its original
internal admissibility and individual-function RH assumptions. The unconditional
psi theorem supplies the remaining arithmetic input through the existing criterion.
This does not assert the original degree-one, vanishing-error specification. -/
theorem generalL_nonvanishing_proof : Extensions.lls_generalL_nonvanishing := by
  exact
    Extensions.GeneralLFunction.generalL_nonvanishing_of_psi
      AnalyticNumberTheory.PrimeSums.psiSecondOrderBound_unconditional

end PseudoPrime.LLS
