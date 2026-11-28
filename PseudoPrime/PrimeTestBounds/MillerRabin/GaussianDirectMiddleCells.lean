/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CellCurvature
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Rational residual comparisons for the nine direct middle cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational inputs to the endpoint and one-sided-curvature comparison.
The analytic residual must independently satisfy these bounds. -/
public structure GaussianResidualCell where
  left : ℚ
  right : ℚ
  lowerLeft : ℚ
  lowerRight : ℚ
  upperCurvature : ℚ

/-- A cell's two endpoint bounds minus the maximum chord loss. -/
@[expose]
public def GaussianResidualCell.reserve (c : GaussianResidualCell) : ℚ :=
  min c.lowerLeft c.lowerRight - c.upperCurvature * (c.right - c.left) ^ 2 / 8

/-- The certified residual information required for a particular cell. -/
@[expose]
public def GaussianResidualCell.AnalyticBounds (c : GaussianResidualCell) (f f' f'' : ℝ → ℝ) :
    Prop :=
  ContinuousOn f (Set.Icc (c.left : ℝ) (c.right : ℝ)) ∧
    (∀ x ∈ Set.Ioo (c.left : ℝ) (c.right : ℝ), HasDerivAt f (f' x) x) ∧
    (∀ x ∈ Set.Ioo (c.left : ℝ) (c.right : ℝ), HasDerivAt f' (f'' x) x) ∧
    (∀ x ∈ Set.Ioo (c.left : ℝ) (c.right : ℝ), f'' x ≤ (c.upperCurvature : ℝ)) ∧
    (c.lowerLeft : ℝ) ≤ f (c.left : ℝ) ∧ (c.lowerRight : ℝ) ≤ f (c.right : ℝ)

/-- The rational reserve is a lower bound throughout the closed cell
whenever the real endpoint and curvature bounds have been proved. -/
public theorem GaussianResidualCell.reserve_le {c : GaussianResidualCell} {f f' f'' : ℝ → ℝ}
    (h : c.AnalyticBounds f f' f'') (hM : 0 ≤ c.upperCurvature) {x : ℝ}
    (hx : x ∈ Set.Icc (c.left : ℝ) (c.right : ℝ)) : (c.reserve : ℝ) ≤ f x := by
  obtain ⟨hc, h₁, h₂, hcurv, hl, hr⟩ := h
  simpa only [GaussianResidualCell.reserve, Rat.cast_min, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_div, Rat.cast_ofNat] using
    Analysis.cell_lower_of_curvature hx (Rat.cast_nonneg.mpr hM) hc h₁ h₂ hcurv
      ((min_le_left _ _).trans hl) ((min_le_right _ _).trans hr)

/-- The two K141 early rows with the curvature polynomials translated at 20. -/
@[expose]
public def gaussianK141Cells : Fin 2 → GaussianResidualCell :=
  ![⟨20, 45 / 2, 9557368900129 / 10 ^ 12, 9362592241244 / 10 ^ 12, 812 / 1000⟩,
    ⟨45 / 2, 25, 9362592241244 / 10 ^ 12, 7145789359648 / 10 ^ 12, 1900 / 1000⟩]

/-- The seven K156 rows with the curvature polynomials translated at 24. -/
@[expose]
public def gaussianK156Cells : Fin 7 → GaussianResidualCell :=
  ![⟨24, 25, 9243117308041 / 10 ^ 12, 9138428790255 / 10 ^ 12, 433 / 1000⟩,
    ⟨25, 26, 9138428790255 / 10 ^ 12, 8810081128843 / 10 ^ 12, 577 / 1000⟩,
    ⟨26, 27, 8810081128843 / 10 ^ 12, 8201786103400 / 10 ^ 12, 1058 / 1000⟩,
    ⟨27, 28, 8201786103400 / 10 ^ 12, 7133726611085 / 10 ^ 12, 2019 / 1000⟩,
    ⟨28, 29, 7133726611085 / 10 ^ 12, 5256532113650 / 10 ^ 12, 3664 / 1000⟩,
    ⟨29, 30, 5256532113650 / 10 ^ 12, 2115370029608 / 10 ^ 12, 6177 / 1000⟩,
    ⟨30, 121 / 4, 2115370029608 / 10 ^ 12, 1067228790951 / 10 ^ 12, 1611 / 1000⟩]

/-- Every K141 cell has admissible curvature and a reserve strictly above one. -/
private theorem k141_reserve_check (i : Fin 2) :
    0 ≤ (gaussianK141Cells i).upperCurvature ∧ 1 < (gaussianK141Cells i).reserve := by
  fin_cases i <;> decide +kernel

/-- Every K156 cell has admissible curvature and a reserve strictly above one. -/
private theorem k156_reserve_check (i : Fin 7) :
    0 ≤ (gaussianK156Cells i).upperCurvature ∧ 1 < (gaussianK156Cells i).reserve := by
  fin_cases i <;> decide +kernel

/-- An explicit source interval contained within a certificate cell
may use that cell's analytical bounds. -/
private theorem contains_subinterval {c : GaussianResidualCell} {a b : ℚ} {t : ℝ} (ha : c.left ≤ a)
    (hb : b ≤ c.right) (ht : t ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    t ∈ Set.Icc (c.left : ℝ) (c.right : ℝ) :=
  ⟨(Rat.cast_le.mpr ha).trans ht.1, ht.2.trans (Rat.cast_le.mpr hb)⟩

/-- The two K141 cells cover the closed interval from 20 to 25. -/
private theorem k141_cell_cover {t : ℝ} (ht : t ∈ Set.Icc (20 : ℝ) 25) :
    ∃ i : Fin 2,
      t ∈ Set.Icc ((gaussianK141Cells i).left : ℝ) ((gaussianK141Cells i).right : ℝ) := by
  by_cases h : t ≤ 45 / 2
  · exact
      ⟨0,
        contains_subinterval (a := 20) (b := 45 / 2) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat, Rat.cast_div] using
              (show t ∈ Set.Icc (20 : ℝ) (45 / 2) from ⟨ht.1, h⟩))⟩
  · exact
      ⟨1,
        contains_subinterval (a := 45 / 2) (b := 25) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat, Rat.cast_div] using
              (show t ∈ Set.Icc (45 / 2 : ℝ) 25 from ⟨le_of_not_ge h, ht.2⟩))⟩

/-- The seven K156 cells cover the closed interval from 24 to 121/4. -/
private theorem k156_cell_cover {t : ℝ} (ht : t ∈ Set.Icc (24 : ℝ) (121 / 4)) :
    ∃ i : Fin 7,
      t ∈ Set.Icc ((gaussianK156Cells i).left : ℝ) ((gaussianK156Cells i).right : ℝ) := by
  by_cases h0 : t ≤ 25
  · exact
      ⟨0,
        contains_subinterval (a := 24) (b := 25) (by decide +kernel) (by decide +kernel)
          (by simpa only [Rat.cast_ofNat] using (show t ∈ Set.Icc (24 : ℝ) 25 from ⟨ht.1, h0⟩))⟩
  by_cases h1 : t ≤ 26
  · exact
      ⟨1,
        contains_subinterval (a := 25) (b := 26) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat] using
              (show t ∈ Set.Icc (25 : ℝ) 26 from ⟨le_of_not_ge h0, h1⟩))⟩
  by_cases h2 : t ≤ 27
  · exact
      ⟨2,
        contains_subinterval (a := 26) (b := 27) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat] using
              (show t ∈ Set.Icc (26 : ℝ) 27 from ⟨le_of_not_ge h1, h2⟩))⟩
  by_cases h3 : t ≤ 28
  · exact
      ⟨3,
        contains_subinterval (a := 27) (b := 28) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat] using
              (show t ∈ Set.Icc (27 : ℝ) 28 from ⟨le_of_not_ge h2, h3⟩))⟩
  by_cases h4 : t ≤ 29
  · exact
      ⟨4,
        contains_subinterval (a := 28) (b := 29) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat] using
              (show t ∈ Set.Icc (28 : ℝ) 29 from ⟨le_of_not_ge h3, h4⟩))⟩
  by_cases h5 : t ≤ 30
  · exact
      ⟨5,
        contains_subinterval (a := 29) (b := 30) (by decide +kernel) (by decide +kernel)
          (by
            simpa only [Rat.cast_ofNat] using
              (show t ∈ Set.Icc (29 : ℝ) 30 from ⟨le_of_not_ge h4, h5⟩))⟩
  exact
    ⟨6,
      contains_subinterval (a := 30) (b := 121 / 4) (by decide +kernel) (by decide +kernel)
        (by
          simpa only [Rat.cast_ofNat, Rat.cast_div] using
            (show t ∈ Set.Icc (30 : ℝ) (121 / 4) from ⟨le_of_not_ge h5, ht.2⟩))⟩

/-- The two K141 checks imply residual greater than one on the whole range. -/
public theorem gaussian_k141_residual_gt_one {f f' f'' : ℝ → ℝ}
    (h : ∀ i, (gaussianK141Cells i).AnalyticBounds f f' f'') {t : ℝ}
    (ht : t ∈ Set.Icc (20 : ℝ) 25) : 1 < f t := by
  obtain ⟨i, hi⟩ := k141_cell_cover ht
  have hr := Rat.cast_lt (K := ℝ).mpr (k141_reserve_check i).2
  exact
    (by simpa only [Rat.cast_one] using hr : 1 < ((gaussianK141Cells i).reserve : ℝ)).trans_le
      (GaussianResidualCell.reserve_le (h i) (k141_reserve_check i).1 hi)

/-- The seven K156 checks imply residual greater than one on the whole range. -/
public theorem gaussian_k156_residual_gt_one {f f' f'' : ℝ → ℝ}
    (h : ∀ i, (gaussianK156Cells i).AnalyticBounds f f' f'') {t : ℝ}
    (ht : t ∈ Set.Icc (24 : ℝ) (121 / 4)) : 1 < f t := by
  obtain ⟨i, hi⟩ := k156_cell_cover ht
  have hr := Rat.cast_lt (K := ℝ).mpr (k156_reserve_check i).2
  exact
    (by simpa only [Rat.cast_one] using hr : 1 < ((gaussianK156Cells i).reserve : ℝ)).trans_le
      (GaussianResidualCell.reserve_le (h i) (k156_reserve_check i).1 hi)

end PseudoPrime.PrimeTestBounds.MillerRabin
