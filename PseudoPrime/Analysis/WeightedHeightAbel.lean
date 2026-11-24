/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteHeightAbel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Abel summation for differentiable height weights -/

public section

namespace PseudoPrime.Analysis.FiniteHeightAbel

/-- Integrating a cutoff weight starts at the larger of the lower endpoint and the height. -/
private theorem cutoff_mul_integral (g : ℝ → ℝ) {a b y : ℝ} (hab : a ≤ b) (hy : y ≤ b) :
    (∫ t in a..b, if y ≤ t then g t else 0) = ∫ t in max a y..b, g t := by
  by_cases hya : y ≤ a
  · rw [max_eq_left hya]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro t ht
    simp only [hya.trans ht.1, ↓reduceIte]
  have hay := lt_of_not_ge hya
  have hs : Set.Ici y ∩ Set.Ioc a b = Set.Icc y b := by
    ext t
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hay.trans_le h.1, h.2⟩⟩
  change (∫ t in a..b, (Set.Ici y).indicator g t) = _
  rw [max_eq_right hay.le, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ici, hs,
    MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hy]

/-- Integrate a continuous scalar weight against a finite height prefix on a closed interval.
Each point contributes its multiplicity times the integral above its clamped height. -/
theorem integral_prefix_mul {ι : Type*} (s : Finset ι) (γ u : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ j ∈ s, γ j ≤ b) {g : ℝ → ℝ} (hg : ContinuousOn g (Set.uIcc a b)) :
    (∫ t in a..b, heightPrefix s γ u t * g t) = ∑ j ∈ s, u j * ∫ t in max a (γ j)..b, g t := by
  simp only [heightPrefix, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum
      (fun j _ ↦ (intervalIntegrable_cutoff (u j) (γ j) a b).mul_continuousOn hg)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← cutoff_mul_integral g hab (hb j hj), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases h : γ j ≤ t <;> simp only [h, ↓reduceIte, zero_mul, mul_zero]

/-- For a differentiable weight, integrate the weighted prefix by evaluating the primitive
at the upper endpoint and at each clamped height. -/
theorem integral_prefix_deriv {ι : Type*} (s : Finset ι) (γ u : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hb : ∀ j ∈ s, γ j ≤ b) {f g : ℝ → ℝ} (hd : ∀ t ∈ Set.Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Set.uIcc a b)) :
    (∫ t in a..b, heightPrefix s γ u t * g t) = ∑ j ∈ s, u j * (f b - f (max a (γ j))) := by
  rw [integral_prefix_mul s γ u hab hb hg]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := max_le hab (hb j hj)
  have hsub : Set.uIcc (max a (γ j)) b ⊆ Set.Icc a b := by
    rw [Set.uIcc_of_le hm]
    exact fun t ht ↦ ⟨(le_max_left _ _).trans ht.1, ht.2⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hd t (hsub ht))
      ((hg.mono (by simpa only [Set.uIcc_of_le hab] using hsub)).intervalIntegrable)]

end PseudoPrime.Analysis.FiniteHeightAbel
