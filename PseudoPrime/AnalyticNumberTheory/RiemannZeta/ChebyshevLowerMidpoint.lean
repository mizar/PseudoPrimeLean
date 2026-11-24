/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteGridApprox

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroHeadSplit

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroHeadError

import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.Arithmetic.IntegratedChebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbove100RH

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadMidpointRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadDistance100
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.NormalizedLowerTail

/-! # Lower psi estimate from the signed midpoint sum at height 100 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem split_signed_head (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) {A T a b C : ℝ} (hA : 0 ≤ A)
    (hAT : A ≤ T) (ha : 0 < a) (hab : a < b)
    (hC :
      (∑ ρ ∈ S.filter (fun ρ ↦ ¬|ρ.im| ≤ T), (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        C) :
    let f : ℂ → ℂ := fun ρ ↦
      (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
    (∑ ρ ∈ S, f ρ).re ≤
      (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ A), f ρ).re +
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
  have hrm := (le_abs_self _).trans (Complex.abs_re_le_norm (∑ ρ ∈ M, f ρ))
  have hru := (le_abs_self _).trans (Complex.abs_re_le_norm (∑ ρ ∈ U, f ρ))
  change (∑ ρ ∈ S, f ρ).re ≤ _
  rw [hs, Complex.add_re, Complex.add_re]
  nlinarith only [hrm, hru, hm'', hu']

private theorem psi1_signed_lower (hRH : RiemannHypothesis) {A T a b C : ℝ} (hA : 0 ≤ A)
    (hAT : A ≤ T) (ha : 1 < a) (hab : a < b)
    (hC :
      ∀ m : ℕ,
        (∑
            ρ ∈
              ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                        (unifiedTauRectangleUpper 2 m)).filter
                    (fun ρ ↦ ¬ρ.re < 0)).filter
                (fun ρ ↦ ¬|ρ.im| ≤ T),
            (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
          C) :
    let f : ℂ → ℂ := fun ρ ↦
      (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1));
    -(Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a - (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a)) ≤
      (∑ ρ ∈ zerosUpTo A, f ρ).re +
        (b - a) *
          (Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A) +
            (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C) +
        1 := by
  classical
  dsimp only
  let S : ℕ → Finset ℂ := fun m ↦
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let f : ℂ → ℂ := fun ρ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
  let B :=
    Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum A) +
      (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * C
  obtain ⟨r, hr, hlim⟩ := psi1_finite_zero_remainder ha hab.le
  have hlim' :=
    ((hlim.sub_const ((b ^ 2 - a ^ 2) / 2)).add_const (Real.log (2 * Real.pi) * (b - a))).neg
  apply le_of_tendsto hlim'
  filter_upwards [unified_head_eventually_eq hA] with m hhead
  have hbound :=
    split_signed_head hRH (S m)
      (fun ρ hρ ↦ (mem_riemannZetaZerosInAnyRectangle_iff.mp (Finset.mem_filter.mp hρ).1).2)
      (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2) hA hAT (zero_lt_one.trans ha) hab (hC m)
  change
    (∑ ρ ∈ S m, f ρ).re ≤ (∑ ρ ∈ (S m).filter (fun ρ ↦ |ρ.im| ≤ A), f ρ).re + (b - a) * B at hbound
  rw [hhead] at hbound
  have hneg :
    (∑ ρ ∈ S m,
        -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
          (ρ * (ρ + 1))) =
      -(∑ ρ ∈ S m, f ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp only [f]
    ring
  change
    -(((b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) +
              (∑ ρ ∈ S m,
                  -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                    (ρ * (ρ + 1))).re +
              r) -
            (b ^ 2 - a ^ 2) / 2 +
          Real.log (2 * Real.pi) * (b - a)) ≤
      _
  rw [hneg, Complex.neg_re]
  linarith only [hbound, (abs_le.mp hr).1]

/-- A signed integrated head budget gives the lower endpoint estimate for psi. -/
private theorem psi_lower_of_head (hRH : RiemannHypothesis) {a b T H : ℝ} (ha : 1 < a) (hab : a < b)
    (hT : 100 ≤ T)
    (hh :
      (∑ ρ ∈ zerosUpTo 100,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
              (ρ * (ρ + 1))).re ≤
        (b - a) * H) :
    b - Chebyshev.psi b ≤
      (b - a) / 2 + Real.log (2 * Real.pi) + H +
        Real.sqrt b * (zeroReciprocalSum T - zeroReciprocalSum 100) +
        (b ^ (3 / 2 : ℝ) + a ^ (3 / 2 : ℝ)) / (b - a) * ordinateTail T +
        1 / (b - a) := by
  have hC :
    ∀ m : ℕ,
      (∑
          ρ ∈
            ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                      (unifiedTauRectangleUpper 2 m)).filter
                  (fun ρ ↦ ¬ρ.re < 0)).filter
              (fun ρ ↦ ¬|ρ.im| ≤ T),
          (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        ordinateTail T := by
    intro m
    let S :=
      ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                (unifiedTauRectangleUpper 2 m)).filter
            (fun ρ ↦ ¬ρ.re < 0)).filter
        (fun ρ ↦ ¬|ρ.im| ≤ T)
    exact
      finite_ordinate_tail_le hRH S T
        (fun ρ hρ ↦
          (mem_riemannZetaZerosInAnyRectangle_iff.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1).2)
        (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2)
        (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  have h := psi1_signed_lower hRH (by norm_num only : (0 : ℝ) ≤ 100) hT ha hab hC
  dsimp only at h
  have hp := (Arithmetic.psi1_bounds (zero_lt_one.trans ha) hab.le).2
  have hw := sub_pos.mpr hab
  have hc := div_mul_cancel₀ (1 : ℝ) hw.ne'
  apply (le_of_mul_le_mul_right _ hw)
  nlinarith only [h, hh, hp, hc]

/-- A signed midpoint upper bound controls the integrated head in the lower smoothing interval. -/
private theorem lower_integrated_head (hRH : RiemannHypothesis) {a b C : ℝ} (ha : 0 < a)
    (hab : a ≤ b)
    (hc :
      (∑ ρ ∈ zerosUpTo 100,
            (riemannZetaZeroMultiplicity ρ : ℂ) * ((↑((a + b) / 2) : ℂ) ^ ρ / ρ)).re ≤
        C) :
    (∑ ρ ∈ zerosUpTo 100,
          (riemannZetaZeroMultiplicity ρ : ℂ) *
            (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1)))).re ≤
      (b - a) * (C + 3640 * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 2 / 24) := by
  obtain ⟨g, hm, hp, hh, hz, _, hu⟩ := low_zero_100_of_signs low_zero_100_sign_changes
  have hd := (zero_head_distance100_lt hRH g hm hp hh hz (zero_count_100_le_58_of_RH hRH) hu).le
  have h := (abs_le.mp (zero_head_midpoint_error hRH (by norm_num only : (0 : ℝ) ≤ 100) ha hab)).2
  have hw := sub_nonneg.mpr hab
  have hf :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg ha.le (-(3 / 2 : ℝ))) (pow_nonneg hw 3))
      (by norm_num only : (0 : ℝ) ≤ 24)
  nlinarith only [h, mul_le_mul_of_nonneg_right hd hf, mul_le_mul_of_nonneg_left hc hw]

/-- The real part of the multiplicity-weighted midpoint sum at height 100. -/
@[expose]
noncomputable def lowerMidpointSum (t : ℝ) : ℝ :=
  (∑ ρ ∈ zerosUpTo 100, (riemannZetaZeroMultiplicity ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)).re

/-- A scalar bound on the signed midpoint sum yields a normalized lower estimate for psi.
The smoothing interval is [a,x] with relative width d and cutoff 2/d. -/
theorem psi_lower_of_midpoint (hRH : RiemannHypothesis) {a x d C : ℝ} (ha : 1 < a) (hx : a < x)
    (hd : 0 < d) (hw : x - a = x * d) (ht : 100 ≤ 2 / d) (hc : lowerMidpointSum ((a + x) / 2) ≤ C) :
    let T := 2 / d
    let v := Real.log (T / (2 * Real.pi))
    let H := C + 3640 * a ^ (-(3 / 2 : ℝ)) * (x - a) ^ 2 / 24
    (x - Chebyshev.psi x) / Real.sqrt x ≤
      ((x - a) / 2 + Real.log (2 * Real.pi) + H + 1 / (x - a)) / Real.sqrt x +
        ((v ^ 2 + 2 * v + 2) / (2 * Real.pi) - 143 / 125 - (3 / 8) / T + 1 / (15 * T ^ 2)) := by
  extract_lets  T v H
  have ha0 := zero_lt_one.trans ha
  have hx0 := ha0.trans hx
  have hi := lower_integrated_head hRH ha0 hx.le hc
  have hp := psi_lower_of_head (H := H) hRH ha hx ht (by simpa only [H, mul_div_assoc] using hi)
  obtain ⟨g, hm, hg, hh, hz, hl, _⟩ := low_zero_100_of_signs low_zero_100_sign_changes
  have hn := (head100_of_count hRH g hm hg hh hz (zero_count_100_le_58_of_RH hRH) hl).1
  have hb := normalized_lower_tail hRH hn ha0.le hx0 hx.le hd hw rfl ht
  have hs := Real.sqrt_pos.mpr hx0
  apply (div_le_iff₀ hs).mpr
  have he := div_mul_cancel₀ ((x - a) / 2 + Real.log (2 * Real.pi) + H + 1 / (x - a)) hs.ne'
  have htail := (div_le_iff₀ hs).mp hb
  dsimp only [v, T] at hp htail he ⊢
  linarith only [hp, htail, he]

/-- A uniform bound on finite high-zero sums and the signed midpoint estimate
give a lower bound for psi on the additive smoothing interval. -/
theorem psi_lower_of_finite_tail (hRH : RiemannHypothesis) {a b B : ℝ} (ha : 1 < a) (hab : a < b)
    (hB :
      ∀ U : Finset ℂ,
        (∀ ρ ∈ U, riemannZeta ρ = 0) →
          (∀ ρ ∈ U, 0 ≤ ρ.re) →
          (∀ ρ ∈ U, 100 < |ρ.im|) →
          ‖∑ ρ ∈ U,
                (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                  (ρ * (ρ + 1))‖ ≤
            B) :
    let H := lowerMidpointSum ((a + b) / 2) + 3640 * a ^ (-(3 / 2 : ℝ)) * (b - a) ^ 2 / 24
    (b - a) * (b - Chebyshev.psi b) ≤
      (b - a) * ((b - a) / 2 + Real.log (2 * Real.pi) + H) + B + 1 := by
  classical
  intro H
  let S := fun m ↦
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let f := fun ρ : ℂ ↦
    (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))
  have hh : (∑ ρ ∈ zerosUpTo 100, f ρ).re ≤ (b - a) * H := by
    simpa only [f, H, mul_div_assoc] using
      (lower_integrated_head hRH (zero_lt_one.trans ha) hab.le (C := lowerMidpointSum ((a + b) / 2))
        le_rfl)
  obtain ⟨r, hr, hlim⟩ := psi1_finite_zero_remainder ha hab.le
  have hbound :
    Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a ≥
      (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) - ((b - a) * H + B) - 1 := by
    apply ge_of_tendsto hlim
    filter_upwards [unified_head_eventually_eq (by norm_num only : (0 : ℝ) ≤ 100)] with m hm
    let U := (S m).filter (fun ρ ↦ ¬|ρ.im| ≤ 100)
    have ht : ‖∑ ρ ∈ U, f ρ‖ ≤ B :=
      hB U
        (fun ρ h ↦
          (mem_riemannZetaZerosInAnyRectangle_iff.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2)
        (fun ρ h ↦ not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2)
        (fun ρ h ↦ lt_of_not_ge (Finset.mem_filter.mp h).2)
    have hs : (∑ ρ ∈ S m, f ρ).re ≤ (b - a) * H + B := by
      rw [← Finset.sum_filter_add_sum_filter_not (S m) (fun ρ ↦ |ρ.im| ≤ 100), hm, Complex.add_re]
      exact add_le_add hh (((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans ht)
    change
      _ ≤
        (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) +
          (∑ ρ ∈ S m,
              -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                (ρ * (ρ + 1))).re +
          r
    simp only [neg_mul, neg_div, Finset.sum_neg_distrib, Complex.neg_re]
    linarith only [hs, (abs_le.mp hr).1]
  nlinarith only [hbound, (Arithmetic.psi1_bounds (zero_lt_one.trans ha) hab.le).2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
