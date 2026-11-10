/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnconditionalZeroSumBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedExplicitBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogNontrivialLedgerLimit

/-! # Exact logarithmic explicit formula

Identify the finite zero-ledger limit with its absolutely convergent zero series.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Every nontrivial zeta zero eventually lies in the expanding unified
rectangles with right edge `τ > 1`. The zero lies in the critical strip and
the rectangle heights tend to infinity. -/
private theorem nontrivial_mem_unified_eventually {τ : ℝ} (hτ : 1 < τ) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ρ ∈
        riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m) := by
  have hr := riemannZeta_zero_re_le_one hz
  have hh : ∀ᶠ m : ℕ in Filter.atTop, |ρ.im| ≤ unifiedContourHeightSeq m :=
    (Filter.tendsto_atTop.1 tendsto_unifiedContourHeightSeq_atTop) |ρ.im|
  filter_upwards [hh] with m hm
  rw [mem_riemannZetaZerosInAnyRectangle_iff]
  refine ⟨?_, hz⟩
  simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc,
    unifiedRectangleLower, unifiedTauRectangleUpper]
  constructor
  · left
    constructor
    · nlinarith only [hre, Nat.cast_nonneg (α := ℝ) m]
    · linarith only [hr, hτ]
  · left
    exact ⟨(abs_le.mp hm).1, (abs_le.mp hm).2⟩

/-- For `x > 1`, the finite logarithmic nontrivial-zero ledgers converge to
the absolutely convergent zero sum. Each zero eventually lies in the rectangle,
and the inverse-square zero mass supplies a summable dominating family. -/
theorem log_zero_tsum_limit {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          riemannZetaLogZeroContribution x ρ)
      Filter.atTop (nhds (∑' ρ : ℂ, nontrivialLogZeroTerm x ρ)) := by
  classical
  let S : ℕ → Finset ℂ := fun m ↦
    riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)
  let f : ℕ → ℂ → ℂ := fun m ρ ↦ if ρ ∈ S m then nontrivialLogZeroTerm x ρ else 0
  have hpoint (ρ : ℂ) :
    Filter.Tendsto (fun m ↦ f m ρ) Filter.atTop (nhds (nontrivialLogZeroTerm x ρ)) := by
    by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
    · have hm := nontrivial_mem_unified_eventually (τ := 2) (by norm_num only) h.1 h.2
      apply tendsto_const_nhds.congr'
      filter_upwards [hm] with m hm
      simp only [f, S, hm, ↓reduceIte]
    · have hz : nontrivialLogZeroTerm x ρ = 0 := by simp only [nontrivialLogZeroTerm, h, ↓reduceIte]
      simp only [f, hz, ite_self]
      exact tendsto_const_nhds
  have hbound :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ρ : ℂ, ‖f m ρ‖ ≤ x * RiemannXi.inversePowerZeroWeight 2 ρ := by
    filter_upwards with m ρ
    by_cases hm : ρ ∈ S m
    · simpa only [f, hm, ↓reduceIte] using norm_nontrivialLogZeroTerm_le hx.le ρ
    · simp only [f, hm, ↓reduceIte, norm_zero]
      exact mul_nonneg (zero_le_one.trans hx.le) (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ)
  have hs := (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left x
  have hlim := tendsto_tsum_of_dominated_convergence hs hpoint hbound
  apply hlim.congr'
  filter_upwards with m
  rw [tsum_eq_sum (s := S m) (fun ρ hρ ↦ by simp only [f, hρ, ↓reduceIte])]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hz := (mem_riemannZetaZerosInAnyRectangle_iff.mp hρ).2
  simp only [f, hρ, ↓reduceIte, nontrivialLogZeroTerm, hz, true_and, not_lt]

/-- For `x > 1`, the logarithmically weighted Mangoldt sum equals its exact
pole contribution, the real part of the nontrivial-zero series and the trivial
zero correction. Uniqueness of limits identifies the signed contour ledger. -/
theorem log_weighted_exact {x : ℝ} (hx : 1 < x) :
    Arithmetic.logWeightedMangoldtSum x =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log x +
          x +
          (∑' ρ : ℂ, nontrivialLogZeroTerm x ρ).re -
        riemannZetaLogTrivialZeroSeries x := by
  have h :=
    tendsto_nhds_unique (tendsto_logNontrivialLedger hx)
      ((Complex.continuous_re.tendsto _).comp (log_zero_tsum_limit hx))
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
