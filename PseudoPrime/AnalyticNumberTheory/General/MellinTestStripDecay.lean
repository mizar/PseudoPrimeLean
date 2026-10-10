/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestDecay
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniform strip decay of compactly supported logarithmic tests

The common compact support gives uniform bounds for every Schwartz seminorm
of the exponentially weighted family. Fourier continuity preserves its
boundedness, giving arbitrary-power Mellin decay throughout a closed strip.
These estimates prepare the horizontal contour limits in the explicit formula.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a compactly supported smooth test, any weighted derivative seminorm
of its exponential weighting is bounded uniformly on a closed real-part interval.
The Leibniz bound and the explicit exponential derivatives give a continuous
majorant on the product of the interval and the common compact support.
Outside that support all derivatives vanish. This proves boundedness of the
weighted family in Schwartz space before applying the Fourier transform. -/
theorem weightedLogTestSchwartz_seminorm_uniform_bound (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (a b : ℝ) (k n : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ σ ∈ Set.Icc a b, SchwartzMap.seminorm ℂ k n (weightedLogTestSchwartz g hc hg σ) ≤ C := by
  let B : ℝ × ℝ → ℝ := fun p ↦
    ‖p.2‖ ^ k *
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖((1 / 2 : ℝ) - p.1) ^ i * Real.exp (((1 / 2 : ℝ) - p.1) * p.2)‖ *
          ‖iteratedFDeriv ℝ (n - i) g p.2‖
  have hB : Continuous B := by
    apply (continuous_snd.norm.pow k).mul
    apply continuous_finsetSum
    intro i _
    exact
      (continuous_const.mul
            (((continuous_const.sub continuous_fst).pow i).mul
                (Real.continuous_exp.comp
                  ((continuous_const.sub continuous_fst).mul continuous_snd))).norm).mul
        ((hg.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : (n - i : ℕ∞) ≤ ⊤))).comp
            continuous_snd).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hc.isCompact).exists_bound_of_continuousOn hB.continuousOn
  refine ⟨max 0 C, le_max_left _ _, fun σ hσ ↦ ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (le_max_left _ _)
  intro x
  rw [weightedLogTestSchwartz_coe]
  by_cases hx : x ∈ tsupport g
  · have hb :=
      norm_iteratedFDeriv_smul_le
        ((contDiff_const.mul contDiff_id).exp :
          ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y : ℝ ↦ Real.exp (((1 / 2 : ℝ) - σ) * y)))
        hg x (n := n) (by exact_mod_cast le_top)
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, id_eq, iteratedDeriv_exp_const_mul] at hb
    have hgder : ∀ i : ℕ, ‖iteratedDeriv (n - i) g x‖ = ‖iteratedFDeriv ℝ (n - i) g x‖ := fun i ↦
      norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm
    simp only [hgder] at hb
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact
      (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg x) k)).trans
        ((le_abs_self (B (σ, x))).trans ((hC (σ, x) ⟨hσ, hx⟩).trans (le_max_right _ _)))
  · have hz : iteratedFDeriv ℝ n (fun y : ℝ ↦ Real.exp (((1 / 2 : ℝ) - σ) * y) • g y) x = 0 := by
      apply Function.notMem_support.mp
      intro hn
      exact hx (tsupport_smul_subset_right _ _ (support_iteratedFDeriv_subset n hn))
    rw [hz, norm_zero, mul_zero]
    exact le_max_left _ _

/-- For a compactly supported smooth test and a closed real-part interval,
every Fourier Schwartz seminorm of the exponentially weighted family has a
positive uniform bound. Uniform source seminorm bounds give von Neumann
boundedness, which the continuous linear Fourier transform preserves.
This removes the real-part dependence from the fixed-line decay estimate. -/
theorem weightedLogTestSchwartz_fourier_seminorm_uniform_bound (g : ℝ → ℂ)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (a b : ℝ) (k n : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ σ ∈ Set.Icc a b,
          SchwartzMap.seminorm ℂ k n
              (FourierTransform.fourier (weightedLogTestSchwartz g hc hg σ)) ≤
            C := by
  let f : ℝ → SchwartzMap ℝ ℂ := weightedLogTestSchwartz g hc hg
  have hp := schwartz_withSeminorms ℂ ℝ ℂ
  have hb : Bornology.IsVonNBounded ℂ (f '' Set.Icc a b) := by
    apply (hp.image_isVonNBounded_iff_seminorm_bounded f).mpr
    intro i
    obtain ⟨C, hC, hbound⟩ := weightedLogTestSchwartz_seminorm_uniform_bound g hc hg a b i.1 i.2
    exact ⟨C + 1, by linarith only [hC], fun σ hσ ↦ lt_of_le_of_lt (hbound σ hσ) (lt_add_one C)⟩
  have hbf := hb.image (SchwartzMap.fourierTransformCLM ℂ)
  rw [Set.image_image] at hbf
  obtain ⟨C, hC, hbound⟩ :=
    (hp.image_isVonNBounded_iff_seminorm_bounded
          (fun σ ↦ SchwartzMap.fourierTransformCLM ℂ (f σ))).mp
      hbf (k, n)
  exact ⟨C, hC, fun σ hσ ↦ (hbound σ hσ).le⟩

/-- For an even compactly supported smooth logarithmic test and a closed strip,
the Mellin transform times any natural power of the absolute height has a
positive uniform bound. Combine the Mellin--Fourier identity and frequency
rescaling with boundedness of the Fourier Schwartz seminorm across the strip.
The fourth-power case dominates quadratic logarithmic-derivative growth
on the horizontal edges of expanding explicit-formula contours. -/
theorem mellin_logarithmicTestWeight_uniform_power_bound (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (a b : ℝ) (k : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ σ ∈ Set.Icc a b,
          ∀ T : ℝ, |T| ^ k * ‖mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := weightedLogTestSchwartz_fourier_seminorm_uniform_bound g hc hg a b k 0
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  refine ⟨(2 * Real.pi) ^ k * C, mul_pos (pow_pos hp k) hC, fun σ hσ T ↦ ?_⟩
  exact
    (mellin_logarithmicTestWeight_power_bound g he hc hg σ T k).trans
      (mul_le_mul_of_nonneg_left (hbound σ hσ) (pow_nonneg hp.le k))

end PseudoPrime.AnalyticNumberTheory.General
