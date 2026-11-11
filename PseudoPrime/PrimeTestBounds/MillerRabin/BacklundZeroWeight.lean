/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundCircle

/-! # Jensen multiplicities of Backlund zeros -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every zero in the closed Jensen disk has multiplicity at least one.
Analyticity on the disk and nonvanishing at its center rule out infinite
order; a zero therefore contributes a positive divisor multiplicity. -/
theorem backlundAux_divisor_pos {T : ℝ} (hT : 2 < T) (N : ℕ) {u : ℂ}
    (hu : u ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) (hz : backlundAux T N u = 0) :
    (1 : ℤ) ≤
      MeromorphicOn.divisor (backlundAux T N) (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) u := by
  let U := Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2
  have hAn : AnalyticOnNhd ℂ (backlundAux T N) U := backlundAux_analytic_disk hT N
  have htop : analyticOrderAt (backlundAux T N) u ≠ ⊤ := by
    intro h
    have hc : (((3 / 2 : ℝ) : ℂ)) ∈ U := Metric.mem_closedBall_self (by norm_num only)
    have heq :=
      hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_closedBall _ _).isPreconnected hu
        (analyticOrderAt_eq_top.mp h)
    exact backlundAux_center_ne_zero T N (heq hc)
  have hzero : analyticOrderAt (backlundAux T N) u ≠ 0 := by
    rw [Ne, (hAn u hu).analyticOrderAt_eq_zero]
    exact fun h => h hz
  have hm :
    ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt (backlundAux T N) u) = (⊤ : WithTop ℤ) ↔
      analyticOrderAt (backlundAux T N) u = ⊤ := by
    rw [← ENat.map_top (Nat.cast : ℕ → ℤ)]
    exact ENat.map_natCast_injective.eq_iff
  have hn : MeromorphicOn.divisor (backlundAux T N) U u ≠ 0 := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAn hu, ne_eq, WithTop.untop₀_eq_zero, not_or,
      ENat.map_natCast_eq_zero, hm]
    exact ⟨hzero, htop⟩
  have hnonneg : 0 ≤ MeromorphicOn.divisor (backlundAux T N) U u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u
  exact Int.add_one_le_iff.mpr (lt_of_le_of_ne hnonneg (Ne.symm hn))

/-- For a finite set of distinct zeros in the Jensen disk, the sum of their
unweighted logarithmic contributions is at most the full multiplicity-weighted
Jensen sum. Every divisor multiplicity is nonnegative and each chosen zero
has multiplicity at least one. -/
theorem backlundAux_zero_weights_le {T : ℝ} (hT : 2 < T) (N : ℕ) (s : Finset ℂ)
    (hs : ∀ u ∈ s, u ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2 ∧ backlundAux T N u = 0) :
    (∑ u ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - u‖⁻¹)) ≤
      ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (backlundAux T N) (Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2) u : ℝ) *
          Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - u‖⁻¹) := by
  classical
  let c : ℂ := (((3 / 2 : ℝ) : ℂ))
  let U := Metric.closedBall c 2
  let d := MeromorphicOn.divisor (backlundAux T N) U
  let w : ℂ → ℝ := fun u => Real.log (2 * ‖c - u‖⁻¹)
  have hAn : AnalyticOnNhd ℂ (backlundAux T N) U := backlundAux_analytic_disk hT N
  have hfin := d.finiteSupport (isCompact_closedBall _ _)
  have hsd : s ⊆ hfin.toFinset := by
    intro u hu
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have hp := backlundAux_divisor_pos hT N (hs u hu).1 (hs u hu).2
    change (1 : ℤ) ≤ d u at hp
    exact ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℤ) < 1) hp)
  have hweight : ∀ u ∈ hfin.toFinset, 0 ≤ w u := by
    intro u hu
    have hus : u ∈ d.support := by simpa only [Set.Finite.mem_toFinset] using hu
    have huU : u ∈ U := d.supportWithinDomain hus
    have hdist : ‖c - u‖ ≤ 2 := by
      simpa only [U, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using huU
    by_cases hz : ‖c - u‖ = 0
    · simp only [w, hz, inv_zero, mul_zero, Real.log_zero, le_refl]
    · have hp : 0 < ‖c - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply Real.log_nonneg
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hp).2 (by simpa only [one_mul] using hdist)
  have hnonneg : ∀ u ∈ hfin.toFinset, 0 ≤ (d u : ℝ) * w u := by
    intro u hu
    exact
      mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn u) (hweight u hu)
  have hsum : (∑ᶠ u, (d u : ℝ) * w u) = ∑ u ∈ hfin.toFinset, (d u : ℝ) * w u := by
    apply finsum_eq_finsetSum_of_support_subset
    intro u hu
    change u ∈ hfin.toFinset
    rw [Set.Finite.mem_toFinset]
    by_contra hd
    have hz : d u = 0 := by simpa only [Function.mem_support, not_ne_iff] using hd
    apply hu
    simp only [hz, Int.cast_zero, zero_mul]
  change (∑ u ∈ s, w u) ≤ ∑ᶠ u, (d u : ℝ) * w u
  rw [hsum]
  calc
    (∑ u ∈ s, w u) ≤ ∑ u ∈ s, (d u : ℝ) * w u := by
      apply Finset.sum_le_sum
      intro u hu
      have hd : (1 : ℝ) ≤ (d u : ℝ) := by
        exact_mod_cast backlundAux_divisor_pos hT N (hs u hu).1 (hs u hu).2
      have hw := hweight u (hsd hu)
      nlinarith only [hd, hw, mul_nonneg (sub_nonneg.mpr hd) hw]
    _ ≤ ∑ u ∈ hfin.toFinset, (d u : ℝ) * w u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsd
      intro u hu _
      exact hnonneg u hu

/-- The logarithmic weights of any finite set of distinct auxiliary zeros
in the Jensen disk are bounded by the explicit circle budget. This combines
the divisor comparison with the Backlund–Jensen upper estimate. -/
theorem backlundAux_zero_weights_budget {T : ℝ} (hT : 17 ≤ T) (N : ℕ) (s : Finset ℂ)
    (hs : ∀ u ∈ s, u ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2 ∧ backlundAux T N u = 0) :
    (∑ u ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - u‖⁻¹)) ≤
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
  exact
    (backlundAux_zero_weights_le (by linarith only [hT]) N s hs).trans
      (backlundAux_jensen_budget hT N)

/-- An injectively indexed finite family of real auxiliary zeros in
`[-1/2, 3/2]` has total Jensen weight at most the explicit circle budget.
The image under the real-to-complex embedding contains distinct zeros in
the Jensen disk, so the finite-zero estimate applies. -/
theorem backlundAux_indexed_weights_budget {T a : ℝ} (hT : 17 ≤ T) (ha : -(1 / 2 : ℝ) ≤ a) (N : ℕ)
    (s : Finset ℝ) (x : ℝ → ℝ) (hinj : Set.InjOn x s)
    (hx : ∀ y ∈ s, x y ∈ Set.Icc a (3 / 2) ∧ backlundAux T N (x y : ℂ) = 0) :
    (∑ y ∈ s, Real.log (2 * ‖(((3 / 2 : ℝ) : ℂ)) - (x y : ℂ)‖⁻¹)) ≤
      (N : ℝ) * ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) := by
  classical
  let f : ℝ → ℂ := fun y => (x y : ℂ)
  have hi : Set.InjOn f s := by
    intro y hy z hz h
    apply hinj hy hz
    exact Complex.ofReal_injective h
  have hmem :
    ∀ u ∈ s.image f, u ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2 ∧ backlundAux T N u = 0 := by
    intro u hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
    have hr := (hx y hy).1
    constructor
    · change (x y : ℂ) ∈ Metric.closedBall (((3 / 2 : ℝ) : ℂ)) 2
      rw [Metric.mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith only [ha, hr.1, hr.2]
    · exact (hx y hy).2
  have h := backlundAux_zero_weights_budget hT N (s.image f) hmem
  rw [Finset.sum_image hi] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
