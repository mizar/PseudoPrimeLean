/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffCertificate
public import PseudoPrime.Analysis.ExponentialFixedPointExecution

/-! # Explicit execution of the finite Gaussian cutoff certificate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The fixed-point density lower value computed using the explicit Taylor state APIs.
This retains the exact specification arithmetic while avoiding repeated prefix sums
in execution. The equality theorem transfers the analytic node bound. -/
def gaussianCutoffNodeLowerParamFast (a b : ℕ) (m : ℤ) : ℕ :=
  let S := gaussianCutoffNodeScale
  let G := S * S / expFixedPointUpperSumFast (m * m).toNat 16000000 S 121
  let T := expFixedPointSignedLowerFast m 8000 S 121
  let Z := expFixedPointSignedLowerFast (-m) 4000 S 121 * a / b
  let P := expFixedPointLowerSumFast Z S S 121
  let C := S - (S * S + P - 1) / P
  let V := G * T / S
  let V := V * C / S
  V * 56418958 / 100000000

/-- The established fast 21/10 node API is the corresponding cutoff specialization. -/
def gaussianCutoffNodeLowerFast (m : ℤ) : ℕ :=
  gaussianCutoffNodeLowerParamFast 21 10 m

/-- The fast parameterized node execution equals its analytic specification. -/
theorem gaussianCutoffNodeLowerParamFast_eq (a b : ℕ) (m : ℤ) :
    gaussianCutoffNodeLowerParamFast a b m = gaussianCutoffNodeLowerParam a b m := by
  simp only [gaussianCutoffNodeLowerParamFast, gaussianCutoffNodeLowerParam,
    expFixedPointUpperSumFast_eq, expFixedPointLowerSumFast_eq, expFixedPointSignedLowerFast_eq]

/-- The explicit node execution API equals its analytic specification at every numerator.
Replace the three Taylor execution calls by their proven equalities. -/
theorem gaussianCutoffNodeLowerFast_eq (m : ℤ) :
    gaussianCutoffNodeLowerFast m = gaussianCutoffNodeLower m := by
  simp only [gaussianCutoffNodeLowerFast, gaussianCutoffNodeLower,
    gaussianCutoffNodeLowerParamFast_eq]

/-- The explicit finite midpoint sum using the state-based node execution API.
Every contribution retains the specification's outward rounding and scale. -/
def gaussianCutoffMidpointLowerFast : ℕ :=
  ∑ k ∈ Finset.range 16000, gaussianCutoffNodeLowerFast (((2 * k + 1 : ℕ) : ℤ) - 16000) / 2000

/-- The explicit finite execution sum equals the proved mathematical certificate.
Replace each node using the exact node execution equality. -/
theorem gaussianCutoffMidpointLowerFast_eq :
    gaussianCutoffMidpointLowerFast = gaussianCutoffMidpointLower := by
  simp only [gaussianCutoffMidpointLowerFast, gaussianCutoffMidpointLower,
    gaussianCutoffNodeLowerFast_eq]

end PseudoPrime.Analysis
