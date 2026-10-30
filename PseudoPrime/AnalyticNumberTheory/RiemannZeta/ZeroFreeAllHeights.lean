/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroFreeLogSquared
public import Mathlib.Topology.MetricSpace.Thickening
/-!
# An all-height squared-log zeta zero-free region

Compactness fills the finite-height part of the previously established high-height strip.
Use the entire pole-removed zeta function so that the pole at one causes no discontinuity.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta
/-- The entire pole-removed zeta function is nonzero on the closed right half-plane.
At one its value is one; elsewhere use zeta nonvanishing and the nonzero pole factor.
This places compact portions of the boundary line inside an open nonvanishing set. -/
theorem regularZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hn
  · rw [riemannZeta₁_one]
    exact one_ne_zero
  have he : riemannZeta₁ s = (s - 1) * riemannZeta s :=
    ((eq_inv_mul_iff_mul_eq₀ (sub_ne_zero.mpr hn)).mp (riemannZeta_eq_inv_sub_mul hn)).symm
  rw [he]
  exact mul_ne_zero (sub_ne_zero.mpr hn) (riemannZeta_ne_zero_of_one_le_re hs)
/-- For any real height bound there is a positive strip width, at most one half,
on which zeta is nonzero up to that absolute height. Thicken the compact image of the
closed height interval in the open nonvanishing set of pole-removed zeta.
This supplies the low-height part missing from the large-height zero-free estimate. -/
theorem exists_zeroFree_bounded_height (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ s : ℂ, |s.im| ≤ T → 1 - δ < s.re → riemannZeta s ≠ 0 := by
  let f : ℝ → ℂ := fun t ↦ 1 + (t : ℂ) * Complex.I
  have hf : Continuous f := continuous_const.add (Complex.continuous_ofReal.mul_const _)
  have hc := (isCompact_Icc : IsCompact (Set.Icc (-T) T)).image hf
  have ho : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    isOpen_ne.preimage differentiable_riemannZeta₁.continuous
  have hsub : f '' Set.Icc (-T) T ⊆ {s : ℂ | riemannZeta₁ s ≠ 0} := by
    rintro s ⟨t, _, rfl⟩
    apply regularZeta_ne_zero_of_one_le_re
    simp only [f, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, le_refl]
  obtain ⟨ε, hε, he⟩ := hc.exists_thickening_subset_open ho hsub
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num only), min_le_right _ _, ?_⟩
  intro s ht hs
  by_cases hre : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hre
  have hre' : s.re < 1 := lt_of_not_ge hre
  have hdist : dist s (f s.im) = |s.re - 1| := by
    have hdiff : s - f s.im = ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [f, Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          zero_mul, sub_zero, add_zero]
      · simp only [f, Complex.sub_im, Complex.add_im, Complex.one_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          mul_one, zero_add, add_zero, sub_self]
    rw [dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hclose : dist s (f s.im) < ε := by
    rw [hdist, abs_of_neg (sub_neg.mpr hre')]
    have hmin := min_le_left ε (1 / 2 : ℝ)
    linarith only [hs, hmin]
  have hreg : riemannZeta₁ s ≠ 0 := he (Metric.mem_thickening_iff.mpr
    ⟨f s.im, ⟨s.im, abs_le.mp ht, rfl⟩, hclose⟩)
  have hn : s ≠ 1 := by
    intro hh
    rw [hh, Complex.one_re] at hre'
    exact lt_irrefl _ hre'
  rw [riemannZeta_eq_inv_sub_mul hn]
  exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hn)) hreg
/-- There is a positive squared-log width such that zeta is nonzero strictly to the
right of the resulting boundary at every height. Take the smaller of the large-height
width and a compact low-height width scaled by log(2) squared.
This removes the entrance-height condition for later contour and zero-sum estimates. -/
theorem exists_zeroFree_all_heights :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ^ 2 < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨ch, T0, hch, _, hh⟩ := exists_zeroFree_log_sq
  obtain ⟨δ, hδ, _, hl⟩ := exists_zeroFree_bounded_height T0
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  let c : ℝ := min ch (δ * Real.log 2 ^ 2)
  have hc : 0 < c := lt_min hch (mul_pos hδ (sq_pos_of_pos hlog))
  refine ⟨c, hc, ?_⟩
  intro s hs
  have hLs : 0 < Real.log (|s.im| + 2) :=
    Real.log_pos (by linarith only [abs_nonneg s.im])
  by_cases ht : T0 ≤ |s.im|
  · apply hh s ht
    have hdiv := div_le_div_of_nonneg_right (min_le_left ch (δ * Real.log 2 ^ 2))
      (sq_nonneg (Real.log (|s.im| + 2)))
    change c / Real.log (|s.im| + 2) ^ 2 ≤ ch / Real.log (|s.im| + 2) ^ 2 at hdiv
    linarith only [hdiv, hs]
  · apply hl s (le_of_not_ge ht)
    have hlogs : Real.log 2 ≤ Real.log (|s.im| + 2) :=
      Real.log_le_log (by norm_num only) (by linarith only [abs_nonneg s.im])
    have hsquares : Real.log 2 ^ 2 ≤ Real.log (|s.im| + 2) ^ 2 := by
      nlinarith only [hlog, hlogs, sq_nonneg (Real.log (|s.im| + 2) - Real.log 2)]
    have hmul := mul_le_mul_of_nonneg_left hsquares hδ.le
    have hcle := min_le_right ch (δ * Real.log 2 ^ 2)
    have hdiv : c / Real.log (|s.im| + 2) ^ 2 ≤ δ :=
      (div_le_iff₀ (sq_pos_of_pos hLs)).mpr (hcle.trans hmul)
    linarith only [hdiv, hs]
/-- There is a positive squared-log width bounding the real parts of every actual
zeta zero at all heights. Apply the all-height nonvanishing region by contradiction.
This is the unconditional real-part input for logarithmic explicit-formula zero terms. -/
theorem exists_zero_gap_all_heights :
    ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 →
        ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2 := by
  obtain ⟨c, hc, hz⟩ := exists_zeroFree_all_heights
  refine ⟨c, hc, fun ρ hρ ↦ ?_⟩
  by_contra h
  exact hz ρ (lt_of_not_ge h) hρ
end PseudoPrime.AnalyticNumberTheory.RiemannZeta
