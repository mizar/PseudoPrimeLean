/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.RiemannLogResidueBound
import PseudoPrime.LLS.RiemannReciprocalResidueBound

/-!
# Shared Riemann lower-bound assembly

RH gives the logarithmic and reciprocal LLS lower bounds used together in character applications.
This assembly is independent of any concrete Jacobi input or witness set.
-/

namespace PseudoPrime.LLS.Extensions

/-- RH supplies both LLS Riemann weighted-sum lower bounds.
The logarithmic estimate and the reciprocal estimate are combined as a conjunction, using
`llsRiemannWeightedLowerBound_of_riemannHypothesis` and
`llsRiemannReciprocalLowerBound_of_riemannHypothesis`. This shared assembly supplies character
applications that require both estimates. -/
theorem riemannBounds_of_riemannHypothesis (hRH : RiemannHypothesis) :
    LLSRiemannWeightedLowerBound ∧ LLSRiemannReciprocalLowerBound := by
  exact
    ⟨llsRiemannWeightedLowerBound_of_riemannHypothesis hRH,
      llsRiemannReciprocalLowerBound_of_riemannHypothesis hRH⟩

end PseudoPrime.LLS.Extensions
