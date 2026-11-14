/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting

/-! # Reciprocal zero sums on height intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `0 ≤ A ≤ T`, the reciprocal zero sum over heights in `(A,T]` is
the difference of the two closed-height sums. Zeros exactly at `A` are
excluded from the interval, while zeros at `T` are included. -/
theorem zeroReciprocal_interval {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T) :
    (∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ A < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) =
      zeroReciprocalSum T - zeroReciprocalSum A := by
  classical
  have heq : (zerosUpTo T).filter (fun ρ ↦ ¬A < |ρ.im|) = zerosUpTo A := by
    ext ρ
    rw [Finset.mem_filter, mem_zerosUpTo (hA.trans hAT), mem_zerosUpTo hA]
    constructor
    · rintro ⟨⟨hz, hre, ht⟩, ha⟩
      exact ⟨hz, hre, le_of_not_gt ha⟩
    · rintro ⟨hz, hre, ha⟩
      exact ⟨⟨hz, hre, ha.trans hAT⟩, not_lt_of_ge ha⟩
  have h :=
    Finset.sum_filter_add_sum_filter_not (zerosUpTo T) (fun ρ : ℂ ↦ A < |ρ.im|)
      (fun ρ ↦ (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|)
  rw [heq, ← zeroReciprocalSum_eq, ← zeroReciprocalSum_eq] at h
  linarith only [h]

/-- For `0 ≤ A ≤ T`, the reciprocal sum over any finite set of zeta zeros
with nonnegative real part and heights in `(A,T]` is bounded by the
difference of the two closed-height reciprocal sums. -/
theorem zeroReciprocal_interval_le (S : Finset ℂ) {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) :
    (∑ ρ ∈ (S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) ≤
      zeroReciprocalSum T - zeroReciprocalSum A := by
  rw [← zeroReciprocal_interval hA hAT]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ρ hρ
    have hh := Finset.mem_filter.mp hρ
    apply Finset.mem_filter.mpr
    exact ⟨(mem_zerosUpTo (hA.trans hAT)).2 ⟨hz ρ hh.1, hre ρ hh.1, hh.2.2⟩, hh.2.1⟩
  · intro ρ hρ hnot
    exact div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
