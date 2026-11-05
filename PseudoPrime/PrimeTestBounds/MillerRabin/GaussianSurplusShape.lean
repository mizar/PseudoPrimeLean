/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusRoots

/-! # Monotone Gaussian surplus comparison functions -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian prime cutoff from a clipped radius. -/
noncomputable def jointSurplusCutoff (rho R L : ℝ) : ℝ :=
  (21 / 10 : ℝ) * jointSurplusRadius rho R L ^ 2

/-- The proposed all-scale minimum of the four-ninths and two surplus cutoffs. -/
noncomputable def jointSurplusGlobal (L : ℝ) : ℝ :=
  min ((4 / 9 : ℝ) * L ^ 2) (min (jointSurplusCutoff 130 30 L) (jointSurplusCutoff 155 29 L))

/-- Each surplus cutoff is nondecreasing in the logarithmic scale. -/
theorem jointSurplusCutoff_mono {rho R L M : ℝ} (hrho : 0 ≤ rho) (hLM : L ≤ M) :
    jointSurplusCutoff rho R L ≤ jointSurplusCutoff rho R M := by
  have hroot : jointSurplusRoot R L ≤ jointSurplusRoot R M := by
    unfold jointSurplusRoot
    apply Analysis.gaussianBudgetRoot_mono (by norm_num only)
    nlinarith only [hLM]
  have hroot0 : 0 ≤ jointSurplusRoot R L :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hsq := pow_le_pow_left₀ hroot0 hroot 2
  have hrad : jointSurplusRadius rho R L ≤ jointSurplusRadius rho R M := max_le_max le_rfl hsq
  have hrad0 : 0 ≤ jointSurplusRadius rho R L := hrho.trans (le_max_left _ _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrad0 hrad 2) (by norm_num only)

/-- On nonnegative scales the proposed global minimum is nondecreasing. -/
theorem jointSurplusGlobal_mono {L M : ℝ} (hL : 0 ≤ L) (hLM : L ≤ M) :
    jointSurplusGlobal L ≤ jointSurplusGlobal M := by
  have hM : 0 ≤ M := hL.trans hLM
  have hs := (sq_le_sq₀ hL hM).mpr hLM
  unfold jointSurplusGlobal
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left hs (by norm_num only)
  · exact
      min_le_min (by exact jointSurplusCutoff_mono (by norm_num only) hLM)
        (by exact jointSurplusCutoff_mono (by norm_num only) hLM)

/-- For positive scales and a nonnegative residual, the clipped radius divided by
the scale is nonincreasing. Compare the quadratic root at the larger scale with a
square-root rescaling of the smaller root, then include the fixed radius floor. -/
theorem jointSurplusRadius_ratio_anti {rho R L M : ℝ} (hrho : 0 ≤ rho) (hR : 0 ≤ R) (hL : 0 < L)
    (hLM : L ≤ M) : jointSurplusRadius rho R M / M ≤ jointSurplusRadius rho R L / L := by
  let D : ℝ := 10971611 / 5000000
  let V : ℝ := 28794111 / 12500000
  let A : ℝ := 20115621 / 25000000
  let s := jointSurplusRoot R L
  let k := Real.sqrt (M / L)
  have hM : 0 < M := hL.trans_le hLM
  have hD : 0 < D := by norm_num only [D]
  have hV : 0 < V := by norm_num only [V]
  have hA : 0 < A := by norm_num only [A]
  have hC : 0 < A * L + R := add_pos_of_pos_of_nonneg (mul_pos hA hL) hR
  have hs : 0 < s := Analysis.gaussianBudgetRoot_pos hD hV
  have he : D * s ^ 2 = V * s + (A * L + R) := Analysis.gaussianBudgetRoot_equation hD hC.le
  have hDs : V < D * s := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hs.le
    nlinarith only [hm, he, hC]
  have hratio : (1 : ℝ) ≤ M / L := (one_le_div hL).mpr hLM
  have hk1 : (1 : ℝ) ≤ k := by
    apply (Real.le_sqrt (by norm_num only) (div_nonneg hM.le hL.le)).mpr
    norm_num only
    exact hratio
  have hk0 : 0 ≤ k := by linarith only [hk1]
  have hk2 : k ^ 2 = M / L := Real.sq_sqrt (div_nonneg hM.le hL.le)
  have hkL : k ^ 2 * L = M := by rw [hk2, div_mul_cancel₀ _ hL.ne']
  have hkk : k ≤ k ^ 2 := by nlinarith only [hk1]
  have hks : s ≤ k * s := by nlinarith only [hk1, hs]
  have hVks : V < D * (k * s) := hDs.trans_le (mul_le_mul_of_nonneg_left hks hD.le)
  have hC_M : 0 ≤ A * M + R := add_nonneg (mul_nonneg hA.le hM.le) hR
  have heMul := congrArg (fun z : ℝ ↦ z * k ^ 2) he
  have hterm1 : 0 ≤ V * s * (k ^ 2 - k) := mul_nonneg (mul_nonneg hV.le hs.le) (sub_nonneg.mpr hkk)
  have hterm2 : 0 ≤ R * (k ^ 2 - 1) := mul_nonneg hR (by nlinarith only [hk1])
  have hbudget : A * M + R + V * (k * s) ≤ D * (k * s) ^ 2 := by
    rw [← hkL]
    nlinarith only [heMul, hterm1, hterm2]
  have hroot : jointSurplusRoot R M ≤ k * s :=
    Analysis.gaussianBudgetRoot_le_of_budget hD hV hC_M hVks hbudget
  have hroot0 : 0 ≤ jointSurplusRoot R M := (Analysis.gaussianBudgetRoot_pos hD hV).le
  have hsq := pow_le_pow_left₀ hroot0 hroot 2
  have hcross : jointSurplusRoot R M ^ 2 * L ≤ s ^ 2 * M := by
    have hmul := mul_le_mul_of_nonneg_right hsq hL.le
    have hid : (k * s) ^ 2 * L = s ^ 2 * M := by
      calc
        _ = s ^ 2 * (k ^ 2 * L) := by ring
        _ = _ := by rw [hkL]
    rw [hid] at hmul
    exact hmul
  have hrad0 : 0 ≤ jointSurplusRadius rho R L := hrho.trans (le_max_left _ _)
  have hcross' : jointSurplusRadius rho R M * L ≤ jointSurplusRadius rho R L * M := by
    unfold jointSurplusRadius
    by_cases hmax : rho ≤ jointSurplusRoot R M ^ 2
    · rw [max_eq_right hmax]
      exact hcross.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM.le)
    · rw [max_eq_left (le_of_not_ge hmax)]
      exact
        (mul_le_mul_of_nonneg_left hLM hrho).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hM.le)
  exact (div_le_div_iff₀ hM hL).mpr hcross'

/-- On positive scales, a surplus cutoff divided by the squared scale is
nonincreasing. Square the nonnegative normalized radius comparison. -/
theorem jointSurplusCutoff_ratio_anti {rho R L M : ℝ} (hrho : 0 ≤ rho) (hR : 0 ≤ R) (hL : 0 < L)
    (hLM : L ≤ M) : jointSurplusCutoff rho R M / M ^ 2 ≤ jointSurplusCutoff rho R L / L ^ 2 := by
  have hM : 0 < M := hL.trans_le hLM
  have hrad0 : 0 ≤ jointSurplusRadius rho R M := hrho.trans (le_max_left _ _)
  have hr := jointSurplusRadius_ratio_anti hrho hR hL hLM
  have hs := pow_le_pow_left₀ (div_nonneg hrad0 hM.le) hr 2
  unfold jointSurplusCutoff
  rw [mul_div_assoc, mul_div_assoc, ← div_pow, ← div_pow]
  exact mul_le_mul_of_nonneg_left hs (by norm_num only)

/-- The global comparison function divided by the squared scale is nonincreasing
on positive scales. The four-ninths branch is constant after normalization. -/
theorem jointSurplusGlobal_ratio_anti {L M : ℝ} (hL : 0 < L) (hLM : L ≤ M) :
    jointSurplusGlobal M / M ^ 2 ≤ jointSurplusGlobal L / L ^ 2 := by
  have hM : 0 < M := hL.trans_le hLM
  unfold jointSurplusGlobal
  rw [← min_div_div_right (sq_nonneg M), ← min_div_div_right (sq_nonneg M), ←
    min_div_div_right (sq_nonneg L), ← min_div_div_right (sq_nonneg L)]
  rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hM.ne'),
    mul_div_cancel_right₀ _ (pow_ne_zero _ hL.ne')]
  exact
    min_le_min le_rfl
      (min_le_min (jointSurplusCutoff_ratio_anti (by norm_num only) (by norm_num only) hL hLM)
        (jointSurplusCutoff_ratio_anti (by norm_num only) (by norm_num only) hL hLM))

end PseudoPrime.PrimeTestBounds.MillerRabin
