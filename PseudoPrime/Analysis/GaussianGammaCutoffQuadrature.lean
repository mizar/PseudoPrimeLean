/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffCurvature

/-! # Gaussian cutoff lower bounds from uniform midpoint sums -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative cutoff l, a uniform grid contained in [-4,4] gives a lower
bound for the full cutoff mass after subtracting the curvature error `nh³/9`,
which follows from the uniform second derivative bound `8/3`. -/
theorem gaussianGammaCutoff_uniform_midpoint_lower {l a h : ℝ} {n : ℕ} (hl : 0 ≤ l) (hh : 0 ≤ h)
    (ha : -4 ≤ a) (hend : a + (n : ℝ) * h ≤ 4) :
    h * (∑ k ∈ Finset.range n, gaussianGammaCutoffIntegrand l (a + ((k : ℝ) + 1 / 2) * h)) -
        (n : ℝ) * ((8 / 3) * h ^ 3 / 24) ≤
      ∫ u in (0 : ℝ)..l, gaussianGammaProfile u / Real.sqrt u := by
  have hcell (k : ℕ) (hk : k < n) (x : ℝ)
    (hx : x ∈ Set.Icc (a + (k : ℝ) * h) (a + ((k + 1 : ℕ) : ℝ) * h)) : x ∈ Set.Icc (-4) 4 := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hkn : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
    constructor
    · nlinarith only [ha, hx.1, mul_nonneg hk0 hh]
    · nlinarith only [hend, hx.2, mul_nonneg (sub_nonneg.mpr hkn) hh]
  have hs :=
    uniform_midpoint_sum_lower_of_second_deriv_ge (f := gaussianGammaCutoffIntegrand l) (f' :=
      gaussianGammaCutoffIntegrandDeriv l) (f'' := gaussianGammaCutoffIntegrandSecondDeriv l) hh
      (fun k hk x hx ↦ hasDerivAt_gaussianGammaCutoffIntegrand l x)
      (fun k hk x hx ↦ hasDerivAt_gaussianGammaCutoffIntegrandDeriv l x)
      (fun k hk x hx ↦ (abs_le.mp (gaussianGammaCutoff_secondDeriv_abs_le hl (hcell k hk x hx))).1)
  exact
    hs.trans
      (gaussianGammaCutoff_interval_le_mass hl
        (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hh)))

/-- At cutoff 6/5, the 128-cell midpoint sum on [-4,4], minus 1/288,
is a lower bound for the full cutoff mass. The error is the exact specialization
of the uniform 8/3 curvature estimate. -/
theorem gaussianGammaCutoff_midpoint_128_lower :
    (1 / 16 : ℝ) *
          (∑ k ∈ Finset.range 128,
            gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16))) -
        1 / 288 ≤
      ∫ u in (0 : ℝ)..(6 / 5), gaussianGammaProfile u / Real.sqrt u := by
  have h :=
    gaussianGammaCutoff_uniform_midpoint_lower (l := 6 / 5) (a := -4) (h := 1 / 16) (n := 128)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only at h
  exact h

/-- Preserve the existing 21/10, 16,000-cell consequence, now with the stronger
uniform curvature estimate. Its original error is weaker than the new midpoint error. -/
theorem gaussianGammaCutoff_midpoint_16000_lower :
    (1 / 2000 : ℝ) *
          (∑ k ∈ Finset.range 16000,
            gaussianGammaCutoffIntegrand (21 / 10) (-4 + ((k : ℝ) + 1 / 2) * (1 / 2000))) -
        97 / 12000000 ≤
      ∫ u in (0 : ℝ)..(21 / 10), gaussianGammaProfile u / Real.sqrt u := by
  have h :=
    gaussianGammaCutoff_uniform_midpoint_lower (l := 21 / 10) (a := -4) (h := 1 / 2000) (n := 16000)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only at h
  linarith only [h]

end PseudoPrime.Analysis
