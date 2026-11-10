/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLowZeroBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedHighZeroBound

/-! # Splitting integrated zero contributions at a height

Combine low- and high-zero estimates for finite ledgers.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, split any finite set of nontrivial zeros at `T ≥ 0` and bound
its width-normalized integrated contribution. The low part uses the proved
reciprocal-height sum, while the high inverse-square sum is bounded by the
explicit hypothesis `C`. Zeros at the cutoff belong to the low part. -/
theorem split_zero_sum_bound (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {T a b C : ℝ} (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a < b)
    (hC :
      (∑ ρ ∈ S.filter (fun ρ ↦ ¬|ρ.im| ≤ T), (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        C) :
    ‖∑ ρ ∈ S,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))‖ /
        (b - a) ≤
      Real.sqrt b * zeroReciprocalSum T + (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C := by
  classical
  let L := S.filter (fun ρ ↦ |ρ.im| ≤ T)
  let H := S.filter (fun ρ ↦ ¬|ρ.im| ≤ T)
  let f : ℂ → ℂ := fun ρ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
  have hL : L ⊆ zerosUpTo T := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp hρ
    exact (mem_zerosUpTo hT).2 ⟨hz ρ hh.1, hre ρ hh.1, hh.2⟩
  have hR : (∑ ρ ∈ L, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im|) ≤ zeroReciprocalSum T := by
    rw [zeroReciprocalSum_eq]
    exact
      Finset.sum_le_sum_of_subset_of_nonneg hL
        (fun ρ _ _ ↦ div_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have hlo :=
    low_sum hRH L (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1) ha hab
  have hlo' : ‖∑ ρ ∈ L, f ρ‖ / (b - a) ≤ Real.sqrt b * zeroReciprocalSum T :=
    hlo.trans (mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg b))
  have hhi : ‖∑ ρ ∈ H, f ρ‖ / (b - a) ≤ (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C :=
    high_sum_of_tail hRH H (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1) ha (lt_trans ha hab) (sub_pos.mpr hab) hC
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ |ρ.im| ≤ T) f
  rw [← hsplit]
  have htriangle :=
    div_le_div_of_nonneg_right (norm_add_le (∑ ρ ∈ L, f ρ) (∑ ρ ∈ H, f ρ)) (sub_nonneg.mpr hab.le)
  rw [add_div] at htriangle
  exact htriangle.trans (add_le_add hlo' hhi)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
