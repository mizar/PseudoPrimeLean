/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Abel summation at finitely many real heights

Finite real-frequency prefixes with values in a complete real normed space.
The integral representation avoids ordering or separating repeated frequencies.
-/

@[expose] public section

namespace PseudoPrime.Analysis.FiniteHeightAbel

/-- The finite vector prefix up to real height t. Repeated heights retain their multiplicities.
This prefix is a finite sum of measurable step functions, used in the Abel integral. -/
noncomputable def heightPrefix {ι E : Type*} [AddCommMonoid E] (s : Finset ι) (γ : ι → ℝ)
    (u : ι → E) (t : ℝ) : E :=
  ∑ j ∈ s, if γ j ≤ t then u j else 0

/-- For any vector and three real heights, the cutoff is interval integrable.
Identify it with a measurable half-line indicator restricted to a finite interval. -/
theorem intervalIntegrable_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : E)
    (γ U T : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ if γ ≤ t then u else 0) MeasureTheory.volume U T := by
  apply intervalIntegrable_iff.mpr
  change MeasureTheory.IntegrableOn ((Set.Ici γ).indicator (fun _ : ℝ ↦ u)) (Set.uIoc U T)
  exact
    (MeasureTheory.integrableOn_const (hs :=
            (measure_Ioc_lt_top (μ := MeasureTheory.volume) (a := min U T) (b := max U T)).ne)
            (hC := enorm_ne_top) :
          MeasureTheory.IntegrableOn (fun _ : ℝ ↦ u) (Set.uIoc U T)).indicator
      measurableSet_Ici

/-- For U < gamma ≤ T, the vector cutoff integrates to (T-gamma) times the vector.
Intersect its half-line with the interval and evaluate the constant vector integral. -/
theorem integral_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (u : E) {γ U T : ℝ} (hU : U < γ) (hT : γ ≤ T) :
    (∫ t : ℝ in U..T, if γ ≤ t then u else 0) = (T - γ) • u := by
  have hs : Set.Ici γ ∩ Set.Ioc U T = Set.Icc γ T := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, lt_of_lt_of_le hU h.1, h.2⟩
  change (∫ t : ℝ in U..T, (Set.Ici γ).indicator (fun _ : ℝ ↦ u) t) = _
  rw [intervalIntegral.integral_of_le (le_trans hU.le hT),
    MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ici, hs, MeasureTheory.setIntegral_const,
    Real.volume_real_Icc_of_le hT]

/-- Every finite real-height vector prefix is interval integrable.
Sum the actual integrable cutoff functions; repeated heights cause no difficulty. -/
theorem intervalIntegrable_prefix {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (γ : ι → ℝ) (u : ι → E) (U T : ℝ) :
    IntervalIntegrable (heightPrefix s γ u) MeasureTheory.volume U T := by
  have h := IntervalIntegrable.sum s (fun j hj ↦ intervalIntegrable_cutoff (u j) (γ j) U T)
  convert h using 1
  funext t
  simp only [heightPrefix, Finset.sum_apply]

/-- If all finite heights lie in (U,T], the prefix integral equals the sum of (T-gamma)u.
Integrate the finite family of cutoffs term by term for vector-valued Abel summation. -/
theorem integral_prefix {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : Finset ι) (γ : ι → ℝ) (u : ι → E) {U T : ℝ} (hU : ∀ j ∈ s, U < γ j)
    (hT : ∀ j ∈ s, γ j ≤ T) :
    (∫ t : ℝ in U..T, heightPrefix s γ u t) = ∑ j ∈ s, (T - γ j) • u j := by
  simp only [heightPrefix]
  rw [intervalIntegral.integral_finsetSum (fun j hj ↦ intervalIntegrable_cutoff (u j) (γ j) U T)]
  exact Finset.sum_congr rfl (fun j hj ↦ integral_cutoff (u j) (hU j hj) (hT j hj))

/-- For vector coefficients at heights in (U,T], the height-weighted sum equals the terminal
sum times T minus the prefix integral. Rearrange the exact finite cutoff integral. -/
theorem weighted_sum_eq {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : Finset ι) (γ : ι → ℝ) (u : ι → E) {U T : ℝ} (hU : ∀ j ∈ s, U < γ j)
    (hT : ∀ j ∈ s, γ j ≤ T) :
    (∑ j ∈ s, γ j • u j) = T • (∑ j ∈ s, u j) - ∫ t : ℝ in U..T, heightPrefix s γ u t := by
  rw [integral_prefix s γ u hU hT]
  simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
  abel

/-- For 0 ≤ U ≤ T and heights in (U,T], a prefix norm bound C implies a weighted-sum
norm bound (2T-U)C. Use the vector Abel identity and the integral norm bound. -/
theorem norm_weighted_sum_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (s : Finset ι) (γ : ι → ℝ) (u : ι → E) {U T C : ℝ} (hU0 : 0 ≤ U) (hUT : U ≤ T)
    (hU : ∀ j ∈ s, U < γ j) (hT : ∀ j ∈ s, γ j ≤ T)
    (hP : ∀ t ∈ Set.Icc U T, ‖heightPrefix s γ u t‖ ≤ C) :
    ‖∑ j ∈ s, γ j • u j‖ ≤ (2 * T - U) * C := by
  have hT0 : 0 ≤ T := le_trans hU0 hUT
  have hlast : heightPrefix s γ u T = ∑ j ∈ s, u j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left (hT j hj)
  have hsum : ‖∑ j ∈ s, u j‖ ≤ C := by
    rw [← hlast]
    exact hP T ⟨hUT, le_rfl⟩
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht ↦ hP t ⟨(Set.uIoc_of_le hUT ▸ ht).1.le, (Set.uIoc_of_le hUT ▸ ht).2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hUT)] at hint
  rw [weighted_sum_eq s γ u hU hT]
  calc
    _ ≤ ‖T • (∑ j ∈ s, u j)‖ + ‖∫ t : ℝ in U..T, heightPrefix s γ u t‖ := norm_sub_le _ _
    _ ≤ T * C + C * (T - U) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT0]
      exact add_le_add (mul_le_mul_of_nonneg_left hsum hT0) hint
    _ = _ := by ring

end PseudoPrime.Analysis.FiniteHeightAbel
