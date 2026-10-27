/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedEulerCertificate

/-! # Exact Euler positivity for a rounded phase-search candidate

The name records its exploratory scale only. No spectral majorant or witness bound
at that scale is asserted here.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: none. Output: ten rational node-coefficient pairs
from the phase-only search at log scale 64.
Definition: coefficients rounded to denominator 100000000 with positive padding at node 6/5.
Role: give a concrete exact Euler certificate; spectral dominance remains unproved. -/
def phaseResolvent64Coefficients : List (ℚ × ℚ) :=
  [(1, 33447047 / 20000000), (6 / 5, 457646463 / 100000000), (7 / 5, -312390849 / 50000000),
    (5 / 2, 95093473 / 20000000), (3, -95093473 / 20000000), (5, 116905279 / 100000000),
    (7, -8327877 / 50000000), (10, -16061581 / 100000000), (15, 4528099 / 50000000),
    (20, -2351311 / 100000000)]

/-- Input: none. Claim: the rational candidate has nodes above one half in sorted order,
and every coefficient prefix is nonnegative.
Proof: kernel-check the finite rational Boolean computation.
Role: certify admissibility and whole-halfline Euler positivity. -/
theorem phaseResolvent64_node_check :
    finiteSignedPhaseNodeCheck phaseResolvent64Coefficients = true := by decide +kernel

/-- Input: any real base at least one.
Claim: the rounded candidate's combined Euler weight is nonnegative.
Proof: apply the generic Abel certificate to the checked rational list.
Role: remove the infinite positivity premise for this prospective phase majorant. -/
theorem phaseResolvent64_euler_nonneg {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ finiteSignedEulerWeight phaseResolvent64Coefficients u := by
  exact
    finiteSignedEulerWeight_nonneg_of_check phaseResolvent64Coefficients
      (finiteSignedPhaseNodeCheck_sound _ phaseResolvent64_node_check).2 hu

end PseudoPrime.Analysis
