/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroSplitBound
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalInterval

/-! # Integrated zero sums with a signed low-height head -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, split a finite nontrivial-zero ledger into a head through `A`,
a middle range `(A,T]` and a tail above `T`. The real part of the head is
retained, while the other ranges use reciprocal and inverse-square bounds. -/
theorem split_zero_sum_retain_head (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {A T a b C : ℝ} (hA : 0 ≤ A)
    (hAT : A ≤ T) (ha : 0 < a) (hab : a < b)
    (hC :
      (∑ ρ ∈ S.filter (fun ρ ↦ ¬|ρ.im| ≤ T), (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        C) :
    let f : ℂ → ℂ := fun ρ ↦
      (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    |(∑ ρ ∈ S, f ρ).re| ≤
      |(∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ A), f ρ).re| +
        (b - a) *
          (Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A) +
            (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C) := by
  classical
  dsimp only
  let f : ℂ → ℂ := fun ρ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
  let H := S.filter (fun ρ ↦ |ρ.im| ≤ A)
  let R := S.filter (fun ρ ↦ ¬|ρ.im| ≤ A)
  let M := S.filter (fun ρ ↦ A < |ρ.im| ∧ |ρ.im| ≤ T)
  let U := S.filter (fun ρ ↦ ¬|ρ.im| ≤ T)
  have heM : R.filter (fun ρ ↦ |ρ.im| ≤ T) = M := by
    ext ρ
    simp only [R, M, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hs, ha⟩, ht⟩
      exact ⟨hs, ha, ht⟩
    · rintro ⟨hs, ha, ht⟩
      exact ⟨⟨hs, ha⟩, ht⟩
  have heU : R.filter (fun ρ ↦ ¬|ρ.im| ≤ T) = U := by
    ext ρ
    simp only [R, U, Finset.mem_filter, not_le]
    constructor
    · rintro ⟨⟨hs, ha⟩, ht⟩
      exact ⟨hs, ht⟩
    · rintro ⟨hs, ht⟩
      exact ⟨⟨hs, lt_of_le_of_lt hAT ht⟩, ht⟩
  have hs1 := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ |ρ.im| ≤ A) f
  have hs2 := Finset.sum_filter_add_sum_filter_not R (fun ρ : ℂ ↦ |ρ.im| ≤ T) f
  rw [heM, heU] at hs2
  have hs : (∑ ρ ∈ S, f ρ) = (∑ ρ ∈ H, f ρ) + (∑ ρ ∈ M, f ρ) + (∑ ρ ∈ U, f ρ) := by
    change (∑ ρ ∈ H, f ρ) + (∑ ρ ∈ R, f ρ) = _ at hs1
    rw [← hs2] at hs1
    rw [← hs1]
    ring
  have hm :=
    low_sum hRH M (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1) ha hab
  have hrec := zeroReciprocal_interval_le S hA hAT hz hre
  have hm' : ‖∑ ρ ∈ M, f ρ‖ / (b - a) ≤ Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A) :=
    hm.trans (mul_le_mul_of_nonneg_left hrec (Real.sqrt_nonneg b))
  have hu :=
    high_sum_of_tail hRH U (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1) ha (lt_trans ha hab) (sub_pos.mpr hab) hC
  have hw : 0 < b - a := sub_pos.mpr hab
  have hm'' := (div_le_iff₀ hw).1 hm'
  have hu' := (div_le_iff₀ hw).1 hu
  have htri := abs_add_le ((∑ ρ ∈ H, f ρ).re) ((∑ ρ ∈ M, f ρ).re + (∑ ρ ∈ U, f ρ).re)
  have htri2 := abs_add_le ((∑ ρ ∈ M, f ρ).re) ((∑ ρ ∈ U, f ρ).re)
  have hrm := Complex.abs_re_le_norm (∑ ρ ∈ M, f ρ)
  have hru := Complex.abs_re_le_norm (∑ ρ ∈ U, f ρ)
  change |(∑ ρ ∈ S, f ρ).re| ≤ _
  rw [hs, Complex.add_re, Complex.add_re]
  have he :
    ((∑ ρ ∈ H, f ρ).re + (∑ ρ ∈ M, f ρ).re) + (∑ ρ ∈ U, f ρ).re =
      (∑ ρ ∈ H, f ρ).re + ((∑ ρ ∈ M, f ρ).re + (∑ ρ ∈ U, f ρ).re) := by
    ring
  rw [he]
  nlinarith only [htri, htri2, hrm, hru, hm'', hu']

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
