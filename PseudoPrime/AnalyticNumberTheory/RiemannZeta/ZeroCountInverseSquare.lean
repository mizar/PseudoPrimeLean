/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound
import PseudoPrime.Analysis.FiniteHeightAbel

/-! # Integrating the zero count against an inverse-square kernel

Evaluate the integral as a finite sum over the closed-height zero ledger.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Integrate the inverse-square kernel above a cutoff inside the interval.
The cutoff indicator reduces the integral to the upper subinterval. -/
private theorem step_high {a b γ : ℝ} (ha : 1 < a) (haγ : a < γ) (hγb : γ ≤ b) :
    (∫ t in a..b, if γ ≤ t then t⁻¹ ^ 2 else 0) = γ⁻¹ - b⁻¹ := by
  have hs : Set.Ici γ ∩ Set.Ioc a b = Set.Icc γ b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, lt_of_lt_of_le haγ h.1, h.2⟩
  change (∫ t in a..b, (Set.Ici γ).indicator (fun t : ℝ ↦ t⁻¹ ^ 2) t) = _
  rw [intervalIntegral.integral_of_le (haγ.le.trans hγb),
    MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ici, hs,
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hγb,
    inv_sq_integral (lt_trans ha haγ) hγb]

/-- Integrate the inverse-square kernel when its cutoff is at or below the
lower endpoint. The indicator then equals one throughout the interval. -/
private theorem step_low {a b γ : ℝ} (ha : 1 < a) (hab : a ≤ b) (hγa : γ ≤ a) :
    (∫ t in a..b, if γ ≤ t then t⁻¹ ^ 2 else 0) = a⁻¹ - b⁻¹ := by
  rw [← inv_sq_integral ha hab]
  apply intervalIntegral.integral_congr
  rw [Set.uIcc_of_le hab]
  intro t ht
  simp only [hγa.trans ht.1, ↓reduceIte]

/-- For `1 < a ≤ b`, the integral of the zero count divided by the square
of the height is a finite sum over zeros of height at most `b`. Each term uses
the larger of the zero height and `a`, so zeros at both endpoints are retained. -/
theorem zeroCount_invSq_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, zeroCount t / t ^ 2) =
      ∑ ρ ∈ zerosUpTo b, (riemannZetaZeroMultiplicity ρ : ℝ) * ((max a |ρ.im|)⁻¹ - b⁻¹) := by
  classical
  let S := zerosUpTo b
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact
      ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1))).pow
          2) |>.continuousWithinAt
  have hI :
    ∀ ρ ∈ S,
      IntervalIntegrable
        (fun t : ℝ ↦ if |ρ.im| ≤ t then (riemannZetaZeroMultiplicity ρ : ℝ) * t⁻¹ ^ 2 else 0)
        MeasureTheory.volume a b := by
    intro ρ hρ
    have h :=
      (Analysis.FiniteHeightAbel.intervalIntegrable_cutoff (riemannZetaZeroMultiplicity ρ : ℝ)
            |ρ.im| a b).mul_continuousOn
        hc
    convert h using 1
    funext t
    by_cases hh : |ρ.im| ≤ t
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, zero_mul]
  have heq :
    (∫ t in a..b, zeroCount t / t ^ 2) =
      ∫ t in a..b,
        ∑ ρ ∈ S, if |ρ.im| ≤ t then (riemannZetaZeroMultiplicity ρ : ℝ) * t⁻¹ ^ 2 else 0 := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro t ht
    dsimp only
    rw [zeroCount_eq_sum]
    have hs : (S.filter (fun ρ ↦ |ρ.im| ≤ t)) = zerosUpTo t := by
      ext ρ
      rw [Finset.mem_filter, mem_zerosUpTo (le_trans (zero_lt_one.trans ha).le hab),
        mem_zerosUpTo (le_trans (zero_lt_one.trans ha).le ht.1)]
      constructor
      · rintro ⟨⟨hz, hre, htop⟩, hcut⟩
        exact ⟨hz, hre, hcut⟩
      · rintro ⟨hz, hre, hcut⟩
        exact ⟨⟨hz, hre, hcut.trans ht.2⟩, hcut⟩
    rw [← hs, Finset.sum_filter, div_eq_mul_inv, ← inv_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ρ hρ
    by_cases hh : |ρ.im| ≤ t
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, zero_mul]
  rw [heq, intervalIntegral.integral_finsetSum hI]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hγb := ((mem_zerosUpTo ((zero_lt_one.trans ha).le.trans hab)).1 hρ).2.2
  have hmul :
    (∫ t in a..b, if |ρ.im| ≤ t then (riemannZetaZeroMultiplicity ρ : ℝ) * t⁻¹ ^ 2 else 0) =
      (riemannZetaZeroMultiplicity ρ : ℝ) * ∫ t in a..b, if |ρ.im| ≤ t then t⁻¹ ^ 2 else 0 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    by_cases hh : |ρ.im| ≤ t
    · simp only [hh, ↓reduceIte]
    · simp only [hh, ↓reduceIte, mul_zero]
  rw [hmul]
  by_cases hh : |ρ.im| ≤ a
  · rw [max_eq_left hh, step_low ha hab hh]
  · have hh' := lt_of_not_ge hh
    rw [max_eq_right hh'.le, step_high ha hh' hγb]

/-- For `1 < a ≤ b`, the change in the nontrivial inverse-height sum equals
the change in the count divided by height plus the integral of the count over
the squared height. Split the finite closed-height ledger at `a` and use the
inverse-square integral formula, retaining zeros on both endpoints. -/
theorem zeroReciprocal_abel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    zeroReciprocalSum b - zeroReciprocalSum a =
      zeroCount b / b - zeroCount a / a + ∫ t in a..b, zeroCount t / t ^ 2 := by
  classical
  let S := zerosUpTo b
  have hs : S.filter (fun ρ ↦ |ρ.im| ≤ a) = zerosUpTo a := by
    ext ρ
    rw [Finset.mem_filter, mem_zerosUpTo ((zero_lt_one.trans ha).le.trans hab),
      mem_zerosUpTo (zero_lt_one.trans ha).le]
    constructor
    · rintro ⟨⟨hz, hre, htop⟩, hcut⟩
      exact ⟨hz, hre, hcut⟩
    · rintro ⟨hz, hre, hcut⟩
      exact ⟨⟨hz, hre, hcut.trans hab⟩, hcut⟩
  rw [zeroCount_invSq_integral ha hab, zeroReciprocalSum_eq, zeroReciprocalSum_eq, zeroCount_eq_sum,
    zeroCount_eq_sum, ← hs, Finset.sum_div, Finset.sum_div, Finset.sum_filter, Finset.sum_filter]
  have heq :
    ∀ ρ ∈ S,
      (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| -
          (if |ρ.im| ≤ a then (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| else 0) =
        (riemannZetaZeroMultiplicity ρ : ℝ) / b -
            (if |ρ.im| ≤ a then (riemannZetaZeroMultiplicity ρ : ℝ) / a else 0) +
          (riemannZetaZeroMultiplicity ρ : ℝ) * ((max a |ρ.im|)⁻¹ - b⁻¹) := by
    intro ρ hρ
    by_cases h : |ρ.im| ≤ a
    · simp only [h, ↓reduceIte, max_eq_left h]
      ring
    · have hh := (lt_of_not_ge h).le
      simp only [h, ↓reduceIte, max_eq_right hh]
      ring
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl heq

/-- Under RH, for `b ≥ 2πe`, bound the inverse-height zero sum by the
upper endpoint count, the inverse-square count integral and `109/480`.
Apply the finite Abel identity and the proved entrance estimate. -/
theorem zeroReciprocal_abel_from_cutoff (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b) :
    zeroReciprocalSum b ≤
      zeroCount b / b + (∫ t in (2 * Real.pi * Real.exp 1)..b, zeroCount t / t ^ 2) +
        109 / 480 := by
  have h0 : (1 : ℝ) < 2 * Real.pi * Real.exp 1 := by
    have hp :=
      mul_le_mul Real.pi_gt_three.le Real.exp_one_gt_two.le (by norm_num only : (0 : ℝ) ≤ 2)
        Real.pi_pos.le
    nlinarith only [hp]
  have hi := zeroReciprocal_abel h0 hb
  have hstart := zeroReciprocal_at_two_pi_e hRH
  linarith only [hi, hstart]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
