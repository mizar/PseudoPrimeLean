/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight

/-! # General analytic bounds and auxiliary constructions -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A concrete good-height sequence `goodHeightSeq j ∈ [8+j, 8+j+1]` (`j : ℕ`), avoiding every
zero `ρ` with `|Im ρ - (8+j)| ≤ 2` by the margin from
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_height`. -/
noncomputable def goodHeightSeq (j : ℕ) : ℝ :=
  (exists_good_height (H := 8 + (j : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg j))).choose

/--
Every selected height lies in `[8+j,9+j]`. This is the interval component of the
existence witness chosen by `goodHeightSeq`; its lower bound proves that the sequence escapes
to infinity.
-/
theorem goodHeightSeq_mem (j : ℕ) : goodHeightSeq j ∈ Set.Icc (8 + (j : ℝ)) (8 + (j : ℝ) + 1) :=
  (exists_good_height (H := 8 + (j : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg j))).choose_spec.1

/--
The chosen height stays at least `1/(4*jensenLogConst*log(10+j))` from the imaginary
part of every zeta zero within distance two of `8+j`. Extract the separation component of
the chosen existence witness; this is the quantitative input for contour-edge bounds.
-/
theorem goodHeightSeq_good (j : ℕ) :
    ∀ ρ : ℂ,
      riemannZeta ρ = 0 →
        |ρ.im - (8 + (j : ℝ))| ≤ 2 →
        1 / (4 * jensenLogConst * Real.log (8 + (j : ℝ) + 2)) ≤ |goodHeightSeq j - ρ.im| :=
  (exists_good_height (H := 8 + (j : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg j))).choose_spec.2

/--
The good-height sequence tends to positive infinity. Each term is bounded below by
`8+j`, whose natural-index cast tends to infinity; monotone comparison transfers that limit.
Later contour estimates use this sequence to avoid zeros while enlarging rectangles.
-/
theorem tendsto_goodHeightSeq_atTop : Filter.Tendsto goodHeightSeq Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun j => (goodHeightSeq_mem j).1) ?_
  exact Filter.tendsto_atTop_add_const_left Filter.atTop 8 tendsto_natCast_atTop_atTop

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
