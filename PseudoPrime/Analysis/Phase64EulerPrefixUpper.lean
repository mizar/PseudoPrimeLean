/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedEulerUpperRows
public import PseudoPrime.Analysis.Phase64EulerPrefixSeed

/-! # Upper bounds from the existing phase-64 prefix seed -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block0 :
    ((phase64PrefixSeedRows.drop 0).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block1 :
    ((phase64PrefixSeedRows.drop 16).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block2 :
    ((phase64PrefixSeedRows.drop 32).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block3 :
    ((phase64PrefixSeedRows.drop 48).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block4 :
    ((phase64PrefixSeedRows.drop 64).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block5 :
    ((phase64PrefixSeedRows.drop 80).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block6 :
    ((phase64PrefixSeedRows.drop 96).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- The selected bounded row block satisfies the rational upper increment
check. Kernel arithmetic verifies the reused intervals without resource overrides. -/
theorem phase64_prefix_upper_block7 :
    ((phase64PrefixSeedRows.drop 112).take 16).Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  decide +kernel

/-- All seed rows have upper allowance at most their saved lower allowance
plus 1/50000. Join the bounded exact rational block checks. -/
theorem phase64_prefix_upper_checks :
    phase64PrefixSeedRows.Forall
      (fun r ↦ r.1.signedUpper phaseResolvent64Coefficients ≤ r.2 + 1 / 50000) := by
  have he :
    phase64PrefixSeedRows =
      (phase64PrefixSeedRows.drop 0).take 16 ++ (phase64PrefixSeedRows.drop 16).take 16 ++
        (phase64PrefixSeedRows.drop 32).take 16 ++
        (phase64PrefixSeedRows.drop 48).take 16 ++
        (phase64PrefixSeedRows.drop 64).take 16 ++
        (phase64PrefixSeedRows.drop 80).take 16 ++
        (phase64PrefixSeedRows.drop 96).take 16 ++
        (phase64PrefixSeedRows.drop 112).take 16 :=
    rfl
  have h1 := List.forall_append.mpr ⟨phase64_prefix_upper_block0, phase64_prefix_upper_block1⟩
  have h2 := List.forall_append.mpr ⟨h1, phase64_prefix_upper_block2⟩
  have h3 := List.forall_append.mpr ⟨h2, phase64_prefix_upper_block3⟩
  have h4 := List.forall_append.mpr ⟨h3, phase64_prefix_upper_block4⟩
  have h5 := List.forall_append.mpr ⟨h4, phase64_prefix_upper_block5⟩
  have h6 := List.forall_append.mpr ⟨h5, phase64_prefix_upper_block6⟩
  have h7 := List.forall_append.mpr ⟨h6, phase64_prefix_upper_block7⟩
  rw [he]
  exact h7

/-- The distinct seed indices cover exactly every positive prime power through
500. Kernel natural arithmetic checks this support equality for the reused data. -/
theorem phase64_prefix_seed_support :
    (phase64PrefixSeedRows.map (fun r ↦ r.1.index)).toFinset =
      (Finset.Ioc 0 500).filter IsPrimePow := by
  decide +kernel

/-- The saved lower allowances plus the checked per-row increments sum to
at most 143/50. Kernel rational arithmetic checks this aggregate upper allowance. -/
theorem phase64_prefix_rational_upper :
    (phase64PrefixSeedRows.map (fun r ↦ r.2 + 1 / 50000)).sum ≤ (143 / 50 : ℚ) := by decide +kernel

end PseudoPrime.Analysis
