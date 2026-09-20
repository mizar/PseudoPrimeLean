import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight

/-! # General analytic bounds and auxiliary constructions -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A concrete good-height sequence `goodHeightSeq j ∈ [8+j, 8+j+1]` (`j : ℕ`), avoiding every
zero `ρ` with `|Im ρ - (8+j)| ≤ 2` by the margin from
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.exists_good_height`. -/
noncomputable def goodHeightSeq (j : ℕ) : ℝ :=
  (exists_good_height (H := 8 + (j : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg j))).choose

theorem goodHeightSeq_mem (j : ℕ) : goodHeightSeq j ∈ Set.Icc (8 + (j : ℝ)) (8 + (j : ℝ) + 1) :=
  (exists_good_height (H := 8 + (j : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg j))).choose_spec.1

theorem goodHeightSeq_good (j : ℕ) :
    ∀ ρ : ℂ,
      riemannZeta ρ = 0 →
        |ρ.im - (8 + (j : ℝ))| ≤ 2 →
        1 / (4 * jensenLogConst * Real.log (8 + (j : ℝ) + 2)) ≤ |goodHeightSeq j - ρ.im| :=
  (exists_good_height (H := 8 + (j : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg j))).choose_spec.2

theorem tendsto_goodHeightSeq_atTop : Filter.Tendsto goodHeightSeq Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono (fun j => (goodHeightSeq_mem j).1) ?_
  exact Filter.tendsto_atTop_add_const_left Filter.atTop 8 tendsto_natCast_atTop_atTop

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
