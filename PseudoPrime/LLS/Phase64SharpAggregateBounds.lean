/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Phase64EndpointCertificates

/-! # Exact precision retained from the certified endpoint aggregates -/

@[expose] public section

namespace PseudoPrime.LLS.Phase64EndpointCertificates

/-- Given the checked ramp blocks and any natural lower bound S for their
aggregate caps, S is below the complete fixed-point ramp sum. Sum the block bounds
and join their consecutive intervals. This retains all aggregate precision. -/
theorem ramp_natural_lower_of_aggregate {S : ℕ} (hr : ∀ i : Fin 16, RampBlockValid i.val)
    (hc : S ≤ ∑ i ∈ Finset.range 16, rampCaps i) :
    S ≤ ∑ n ∈ Finset.Ioc 0 4096, phase64RampFixedLower n := by
  have hs :
    (∑ i ∈ Finset.range 16, rampCaps i) ≤
      ∑ i ∈ Finset.range 16, ∑ n ∈ Finset.Ioc (256 * i) (256 * (i + 1)), phase64RampFixedLower n :=
    Finset.sum_le_sum (fun i hi ↦ hr ⟨i, Finset.mem_range.mp hi⟩)
  rw [Analysis.sum_Ioc_equal_blocks] at hs
  exact hc.trans hs

/-- Given checked principal blocks and any natural upper bound S for their
aggregate caps, the complete fixed-point principal sum is at most S. Join the
blocks and use the cap comparison. This avoids rounding the final cap to an integer. -/
theorem principal_natural_upper_of_aggregate {S : ℕ} (hp : ∀ i : Fin 32, PrincipalBlockValid i.val)
    (hc : (∑ i ∈ Finset.range 32, principalCaps i) ≤ S) :
    (∑ n ∈ Finset.range 40000, phase64PrincipalFixedUpper n) ≤ S := by
  have hs :
    (∑ i ∈ Finset.range 32,
        ∑ n ∈ Finset.Ico (1250 * i) (1250 * (i + 1)), phase64PrincipalFixedUpper n) ≤
      ∑ i ∈ Finset.range 32, principalCaps i :=
    Finset.sum_le_sum (fun i hi ↦ (hp ⟨i, Finset.mem_range.mp hi⟩).2)
  rw [Analysis.sum_Ico_equal_blocks, Nat.Ico_zero_eq_range] at hs
  exact hs.trans hc

/-- Given checked ramp and principal blocks and an aggregate lower cap S,
the actual ramp at the lower endpoint is at least S/10^10. Transfer the certified
log checks and natural atom sum through the fixed-point soundness theorem. -/
theorem ramp_endpoint_lower_of_aggregate {S : ℕ} (hr : ∀ i : Fin 16, RampBlockValid i.val)
    (hp : ∀ i : Fin 32, PrincipalBlockValid i.val) (hc : S ≤ ∑ i ∈ Finset.range 16, rampCaps i) :
    (S : ℝ) / 10000000000 ≤ exponentialRampMangoldtSum (163840 / 99) := by
  have hlog := principal_log_checks_of_blocks hp
  have hsub : ∀ n ∈ Finset.Ioc 0 4096, phase64EndpointLogCheck n = true := by
    intro n hn
    exact
      hlog n
        (Finset.mem_range.mpr ((Finset.mem_Ioc.mp hn).2.trans_lt (by norm_num only : 4096 < 40000)))
  have hs := phase64_ramp_fixed_sum_sound hsub
  have hn := (Nat.cast_le (α := ℝ)).mpr (ramp_natural_lower_of_aggregate hr hc)
  nlinarith only [hs, hn]

/-- Given checked principal blocks and aggregate upper cap S, the actual
range-40000 exponential Mangoldt sum is at most S/10^10. Apply the existing atom
soundness and natural sum bound. No individual atom is recomputed. -/
theorem principal_endpoint_upper_of_aggregate {S : ℕ} (hp : ∀ i : Fin 32, PrincipalBlockValid i.val)
    (hc : (∑ i ∈ Finset.range 32, principalCaps i) ≤ S) :
    (∑ n ∈ Finset.range 40000,
        Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
      (S : ℝ) / 10000000000 := by
  have hs := phase64_principal_fixed_sum_sound (principal_log_checks_of_blocks hp)
  have hn := (Nat.cast_le (α := ℝ)).mpr (principal_natural_upper_of_aggregate hp hc)
  nlinarith only [hs, hn]

end PseudoPrime.LLS.Phase64EndpointCertificates
