/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedFixedCumulative

/-! # Certified triangular radius lower bounds for fixed-profile windows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational lower certificate for the triangular radius over a bounded scale interval.
The eighth-root and square-root ceilings bound the costs from below. -/
theorem fixed_radius_lower {L U S M c : ℝ} (hL : 30000000000 ≤ L) (hU : L ≤ U) (hS : 0 < S)
    (hM : 0 < M) (hc : 0 < c) (hsq : U ≤ S ^ 2) (hm8 : (5313 / 10000 : ℝ) * U ≤ M ^ 8)
    (hcert :
      (68 - 3 / 10000 : ℝ) * c ^ 2 <
        (36 + (1456 + 13 / 10000000) / S + 165102 / U) * c +
          (4000000000000 * (1001 / 1000)) / (M * U)) :
    c < triangularAdaptiveRadius L := by
  have hp : 0 < L := by linarith only [hL]
  have hU0 : 0 < U := by linarith only [hL, hU]
  have hs : Real.sqrt L ≤ S := (Real.sqrt_le_iff).2 ⟨hS.le, hU.trans hsq⟩
  have hm := triangularEighthRoot_pow hp.le
  have hm0 : 0 ≤ triangularEighthRoot L := Real.sqrt_nonneg _
  have hmp : 0 < triangularEighthRoot L := by
    have hh := triangularEighthRoot_ge_18 hL
    linarith only [hh]
  have hmU : triangularEighthRoot L ≤ M := by
    apply (pow_le_pow_iff_left₀ hm0 hM.le (by norm_num only : (8 : ℕ) ≠ 0)).mp
    rw [hm.2]
    nlinarith only [hU, hm8]
  have hden : triangularEighthRoot L * L ≤ M * U := mul_le_mul hmU hU hp.le hM.le
  have hden0 : 0 < triangularEighthRoot L * L := mul_pos hmp hp
  have ha : (1456 + 13 / 10000000 : ℝ) / S ≤ (1456 + 13 / 10000000) / Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num only) (Real.sqrt_pos.2 hp) hs
  have hb : (165102 : ℝ) / U ≤ 165102 / L := div_le_div_of_nonneg_left (by norm_num only) hp hU
  have hd : (4000000000000 * (1001 / 1000) : ℝ) / (M * U) ≤ triangularAdaptiveD L :=
    div_le_div_of_nonneg_left (by norm_num only) hden0 hden
  have ha' :
    (36 + (1456 + 13 / 10000000 : ℝ) / S + 165102 / U) * c ≤ triangularAdaptiveA L * c := by
    dsimp only [triangularAdaptiveA]
    exact mul_le_mul_of_nonneg_right (by linarith only [ha, hb]) hc.le
  have hbudget :
    (68 - 3 / 10000 : ℝ) * c ^ 2 < triangularAdaptiveA L * c + triangularAdaptiveD L := by
    linarith only [hcert, ha', hd]
  have hbud := triangularAdaptive_budget hL
  have hr := triangularPositiveRoot_spec (K := 68 - 3 / 10000) (by norm_num only) hbud.1 hbud.2.1
  have hroot :
    c <
      triangularPositiveRoot (68 - 3 / 10000) (triangularAdaptiveA L) (triangularAdaptiveD L) := by
    by_contra hn
    have hh :=
      triangular_root_budget (by norm_num only : (0 : ℝ) < 68 - 3 / 10000) hbud.2.1 hr.1 hr.2
        (le_of_not_gt hn) hc
    have hdiv :=
      (div_le_iff₀ hc).mp
        (show triangularAdaptiveD L / c ≤ (68 - 3 / 10000) * c - triangularAdaptiveA L by
          linarith only [hh])
    nlinarith only [hdiv, hbudget]
  exact hroot.trans_le (le_max_right _ _)

/-- The adaptive triangular coefficient exceeds `3869 / 10000` on the stated interval. -/
theorem fixed_radius_03869 {L : ℝ} (hL : (50000000000 : ℝ) ≤ L) (hU : L ≤ 50400000000) :
    (3869 / 10000 : ℝ) < triangularAdaptiveRadius L ^ 2 := by
  have hr :=
    fixed_radius_lower (L := L) (U := 50400000000) (S := 224500) (M := 20113 / 1000) (c :=
      622013 / 1000000) (by linarith only [hL]) hU (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 622013 / 1000000)
          (by linarith only [hr] : 0 ≤ triangularAdaptiveRadius L)).2
      hr
  nlinarith only [hs]

/-- The adaptive triangular coefficient exceeds `222 / 625` on the stated interval. -/
theorem fixed_radius_03552 {L : ℝ} (hL : (70000000000 : ℝ) ≤ L) (hU : L ≤ 70400000000) :
    (222 / 625 : ℝ) < triangularAdaptiveRadius L ^ 2 := by
  have hr :=
    fixed_radius_lower (L := L) (U := 70400000000) (S := 265330) (M := 20971 / 1000) (c :=
      595987 / 1000000) (by linarith only [hL]) hU (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 595987 / 1000000)
          (by linarith only [hr] : 0 ≤ triangularAdaptiveRadius L)).2
      hr
  nlinarith only [hs]

/-- The adaptive triangular coefficient exceeds `1567 / 5000` on the stated interval. -/
theorem fixed_radius_03134 {L : ℝ} (hL : (150000000000 : ℝ) ≤ L) (hU : L ≤ 150100000000) :
    (1567 / 5000 : ℝ) < triangularAdaptiveRadius L ^ 2 := by
  have hr :=
    fixed_radius_lower (L := L) (U := 150100000000) (S := 387428) (M := 23053 / 1000) (c :=
      559822 / 1000000) (by linarith only [hL]) hU (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 559822 / 1000000)
          (by linarith only [hr] : 0 ≤ triangularAdaptiveRadius L)).2
      hr
  nlinarith only [hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
