/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64EndpointCertificates.Data

/-! # Soundness of compact endpoint block certificates -/

@[expose] public section

namespace PseudoPrime.Analysis.Phase64EndpointCertificates

/-- The sixteen saved natural lower caps sum to at least 1514*10^10.
Exact kernel arithmetic checks only the compact aggregate list. -/
theorem ramp_caps_sum : 1514 * 10000000000 ≤ ∑ i ∈ Finset.range 16, rampCaps.getD i 0 := by
  decide +kernel

/-- The thirty-two saved natural upper caps sum to at most 1654*10^10.
Exact kernel arithmetic checks the compact list without recomputing atoms. -/
theorem principal_caps_sum :
    (∑ i ∈ Finset.range 32, principalCaps.getD i 0) ≤ 1654 * 10000000000 := by decide +kernel

/-- Checked ramp blocks imply the complete natural lower sum exceeds
1514*10^10. Sum their inequalities and join consecutive right-closed intervals. -/
theorem ramp_natural_lower_of_blocks (h : ∀ i : Fin 16, RampBlockValid i.val) :
    1514 * 10000000000 ≤ ∑ n ∈ Finset.Ioc 0 4096, phase64RampFixedLower n := by
  have hs :
    (∑ i ∈ Finset.range 16, rampCaps.getD i 0) ≤
      ∑ i ∈ Finset.range 16, ∑ n ∈ Finset.Ioc (256 * i) (256 * (i + 1)), phase64RampFixedLower n :=
    Finset.sum_le_sum (fun i hi ↦ h ⟨i, Finset.mem_range.mp hi⟩)
  rw [sum_Ioc_equal_blocks] at hs
  exact ramp_caps_sum.trans hs

/-- Checked principal blocks imply the complete natural upper sum is
at most 1654*10^10. Join consecutive half-open intervals and compare aggregate caps. -/
theorem principal_natural_upper_of_blocks (h : ∀ i : Fin 32, PrincipalBlockValid i.val) :
    (∑ n ∈ Finset.range 40000, phase64PrincipalFixedUpper n) ≤ 1654 * 10000000000 := by
  have hs :
    (∑ i ∈ Finset.range 32,
        ∑ n ∈ Finset.Ico (1250 * i) (1250 * (i + 1)), phase64PrincipalFixedUpper n) ≤
      ∑ i ∈ Finset.range 32, principalCaps.getD i 0 :=
    Finset.sum_le_sum (fun i hi ↦ (h ⟨i, Finset.mem_range.mp hi⟩).2)
  rw [sum_Ico_equal_blocks, Nat.Ico_zero_eq_range] at hs
  exact hs.trans principal_caps_sum

/-- Principal block validity covers all logarithm checks below 40000.
Use the generic quotient-block property transfer instead of recomputing every check. -/
theorem principal_log_checks_of_blocks (h : ∀ i : Fin 32, PrincipalBlockValid i.val) :
    ∀ n ∈ Finset.range 40000, phase64EndpointLogCheck n = true := by
  have hc :=
    forall_Ico_of_equal_blocks (d := 1250) (k := 32) (by norm_num only) (fun i hi ↦ (h ⟨i, hi⟩).1)
  change ∀ n ∈ Finset.Ico 0 40000, phase64EndpointLogCheck n = true at hc
  rw [Nat.Ico_zero_eq_range] at hc
  exact hc

/-- Given all ramp and principal block proofs, the actual lower-endpoint
ramp sum is at least 1514. Transfer log checks to its support, apply the proved fixed-point
sum inequality and cast the checked natural total. -/
theorem phase64_ramp_endpoint_lower_of_blocks (hr : ∀ i : Fin 16, RampBlockValid i.val)
    (hp : ∀ i : Fin 32, PrincipalBlockValid i.val) :
    (1514 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (163840 / 99) := by
  have hlog := principal_log_checks_of_blocks hp
  have hc : ∀ n ∈ Finset.Ioc 0 4096, phase64EndpointLogCheck n = true := by
    intro n hn
    exact
      hlog n
        (Finset.mem_range.mpr ((Finset.mem_Ioc.mp hn).2.trans_lt (by norm_num only : 4096 < 40000)))
  have hs := phase64_ramp_fixed_sum_sound hc
  have hn := (Nat.cast_le (α := ℝ)).mpr (ramp_natural_lower_of_blocks hr)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hn
  nlinarith only [hs, hn]

/-- Given all principal block proofs, the actual range-40000 exponential
sum at the upper endpoint is at most 1654. Apply fixed-point atom soundness and cast
the checked natural upper total. -/
theorem phase64_principal_endpoint_upper_of_blocks (hp : ∀ i : Fin 32, PrincipalBlockValid i.val) :
    (∑ n ∈ Finset.range 40000,
        Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
      (1654 : ℝ) := by
  have hs := phase64_principal_fixed_sum_sound (principal_log_checks_of_blocks hp)
  have hn := (Nat.cast_le (α := ℝ)).mpr (principal_natural_upper_of_blocks hp)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hn
  nlinarith only [hs, hn]

end PseudoPrime.Analysis.Phase64EndpointCertificates
