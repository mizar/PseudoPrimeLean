/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedExplicitBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnconditionalZeroSumBounds

/-! # Unconditional cutoff errors for the weighted Mangoldt sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta
/-- For an all-height zero gap, x at least one and positive height cutoff, every
unified finite zeta logarithmic residue ledger has error controlled by the unconditional
low-zero and high-tail budgets after the Mellin poles and trivial zeros are removed.
Split the actual finite zero ledger; this is the input for taking the contour limit. -/
theorem abs_logResidueLedger_cutoff_error {c x T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 →
      ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2)
    (hx : 1 ≤ x) (hT : 0 < T) (m : ℕ) :
    |(riemannZetaLogContourResidueLedger x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper 2 m)).re -
      (riemannZetaLogResidueAtZero x +
        riemannZetaLogResidueAtOne x).re -
      (∑ ρ ∈ (riemannZetaZerosInAnyRectangle
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper 2 m)).filter
          (fun ρ : ℂ ↦ ρ.re < 0),
        riemannZetaLogZeroContribution x ρ).re| ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) *
        (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ) +
      x * T ^ (-(1 : ℝ) / 2) *
        ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
  classical
  let S := riemannZetaZerosInAnyRectangle
    (unifiedRectangleLower m)
    (unifiedTauRectangleUpper 2 m)
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ ρ.re < 0)
    (riemannZetaLogZeroContribution x)
  have hb := norm_sum_logZero_split_le hc hg hx hT
    (S.filter (fun ρ : ℂ ↦ ¬ρ.re < 0))
    (fun ρ hρ ↦ (mem_riemannZetaZerosInAnyRectangle_iff.mp
      (Finset.mem_filter.mp hρ).1).2)
    (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp hρ).2)
  rw [riemannZetaLogContourResidueLedger_unifiedTau_eq
    (by norm_num only : (1 : ℝ) < 2), Complex.add_re]
  change |(riemannZetaLogResidueAtZero x +
      riemannZetaLogResidueAtOne x).re +
      (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re -
      (riemannZetaLogResidueAtZero x +
        riemannZetaLogResidueAtOne x).re -
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ρ.re < 0),
        riemannZetaLogZeroContribution x ρ).re| ≤ _
  have hr := congrArg Complex.re hsplit
  rw [Complex.add_re] at hr
  have he : (riemannZetaLogResidueAtZero x +
      riemannZetaLogResidueAtOne x).re +
      (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re -
      (riemannZetaLogResidueAtZero x +
        riemannZetaLogResidueAtOne x).re -
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ρ.re < 0),
        riemannZetaLogZeroContribution x ρ).re =
      (∑ ρ ∈ S.filter (fun ρ : ℂ ↦ ¬ρ.re < 0),
        riemannZetaLogZeroContribution x ρ).re := by
    linarith only [hr]
  rw [he]
  exact (Complex.abs_re_le_norm _).trans hb
/-- Given an all-height zero gap, x greater than one and positive height cutoff,
the actual logarithmically weighted Mangoldt sum differs from its Mellin-pole terms
and trivial-zero correction by at most the unconditional zero budget. Pass the uniform
finite-ledger estimate through the established contour limit. No RH is used. -/
theorem logWeighted_cutoff_error_le {c x T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 →
      ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2)
    (hx : 1 < x) (hT : 0 < T) :
    |Arithmetic.logWeightedMangoldtSum x -
      (riemannZetaLogResidueAtZero x +
        riemannZetaLogResidueAtOne x).re +
      riemannZetaLogTrivialZeroSeries x| ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) *
        (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ) +
      x * T ^ (-(1 : ℝ) / 2) *
        ∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ := by
  have hR := Analysis.tendsto_residueLedger_of_normalized
    (tendsto_riemannZetaLogContourResidueLedger_atTop
      hx (by norm_num only : (1 : ℝ) < 2) le_rfl)
  rw [← logWeightedMangoldtSum_eq_integral
    (zero_lt_one.trans hx) (by norm_num only : (1 : ℝ) < 2)] at hR
  have hRe := (Complex.continuous_re.tendsto _).comp hR
  simp only [Complex.ofReal_re] at hRe
  have ht := tendsto_sum_logTrivialZeros_unifiedRectangle
    hx (by norm_num only : (1 : ℝ) < 2)
  have hlim := ((hRe.sub_const
    (riemannZetaLogResidueAtZero x +
      riemannZetaLogResidueAtOne x).re).sub ht).abs
  have hb := le_of_tendsto hlim (Filter.Eventually.of_forall
    (fun m ↦ abs_logResidueLedger_cutoff_error hc hg hx.le hT m))
  simpa only [sub_neg_eq_add] using hb
/-- For x greater than one, bound the norm of the logarithmic kernel residue at zero
by the fixed second logarithmic derivative plus the absolute log(2*pi) coefficient
times log x. Use its closed form and the triangle inequality. This retains a fixed
logarithmic correction in the unconditional main-term error. -/
theorem norm_logResidueAtZero_le {x : ℝ} (hx : 1 < x) :
    ‖riemannZetaLogResidueAtZero x‖ ≤
      ‖RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero‖ +
        |Real.log (2 * Real.pi)| * Real.log x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hpx : ‖Complex.log (x : ℂ)‖ = Real.log x := by
    rw [← Complex.ofReal_log hx0.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx.le)]
  have hpp : ‖Complex.log (2 * (Real.pi : ℂ))‖ = |Real.log (2 * Real.pi)| := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul,
      ← Complex.ofReal_log (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) Real.pi_pos.le),
      Complex.norm_real, Real.norm_eq_abs]
  rw [riemannZetaLogResidueAtZero_eq hx0]
  have h := norm_sub_le
    (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero)
    (Complex.log (2 * (Real.pi : ℂ)) * Complex.log (x : ℂ))
  rw [norm_neg, norm_mul, hpx, hpp] at h
  exact h
/-- Given a positive all-height zero gap, the actual weighted Mangoldt sum at x
greater than one has main-term error bounded by the low-zero budget, the high-zero tail,
and an explicit fixed multiple of one plus log x. Bound the origin residue and trivial
series. This supplies an unconditional quantitative arithmetic estimate once the gap is chosen. -/
theorem logWeighted_main_error_le {c x T : ℝ} (hc : 0 < c)
    (hg : ∀ ρ : ℂ, riemannZeta ρ = 0 →
      ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2)
    (hx : 1 < x) (hT : 0 < T) :
    |Arithmetic.logWeightedMangoldtSum x - x| ≤
      x ^ (1 - c / Real.log (T + 2) ^ 2) *
        (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ) +
      x * T ^ (-(1 : ℝ) / 2) *
        (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ) +
      (‖RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero‖ +
        |Real.log (2 * Real.pi)| + Real.pi ^ 2 / 24) * (1 + Real.log x) := by
  have hb := logWeighted_cutoff_error_le hc hg hx hT
  rw [riemannZetaLogResidueAtOne_eq] at hb
  have ht0 : 0 ≤ riemannZetaLogTrivialZeroSeries x := by
    apply tsum_nonneg
    intro k
    exact div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hx).le) _)
      (mul_nonneg (by norm_num only) (sq_nonneg _))
  have ht :=
    riemannZetaLogTrivialZeroSeries_le_pi_sq_div_twenty_four hx
  have hR := norm_logResidueAtZero_le hx
  have hreal := Complex.abs_re_le_norm
    (riemannZetaLogResidueAtZero x)
  have htri : |Arithmetic.logWeightedMangoldtSum x - x| ≤
      |Arithmetic.logWeightedMangoldtSum x -
        (riemannZetaLogResidueAtZero x + (x : ℂ)).re +
        riemannZetaLogTrivialZeroSeries x| +
      (‖riemannZetaLogResidueAtZero x‖ +
        riemannZetaLogTrivialZeroSeries x) := by
    have he : Arithmetic.logWeightedMangoldtSum x - x =
        (Arithmetic.logWeightedMangoldtSum x -
          (riemannZetaLogResidueAtZero x + (x : ℂ)).re +
          riemannZetaLogTrivialZeroSeries x) +
        ((riemannZetaLogResidueAtZero x).re -
          riemannZetaLogTrivialZeroSeries x) := by
      rw [Complex.add_re, Complex.ofReal_re]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (le_refl _)
      ((abs_sub _ _).trans (add_le_add hreal (by rw [abs_of_nonneg ht0]))))
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hn := mul_nonneg
    (norm_nonneg RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero) hlog
  have hp := mul_nonneg (div_nonneg (sq_nonneg Real.pi)
    (by norm_num only : (0 : ℝ) ≤ 24)) hlog
  nlinarith only [htri, hb, hR, ht, hn, hp, abs_nonneg (Real.log (2 * Real.pi))]
/-- There are positive zero-gap width and nonnegative mass and correction constants
such that the actual weighted Mangoldt sum has the stated cutoff error for every
x greater than one and positive T. Instantiate the all-height zeta zero-free theorem
and unconditional xi power masses. No RH, GRH or PNT-error hypothesis remains. -/
theorem exists_logWeighted_cutoff_bound :
    ∃ (c C M A : ℝ), 0 < c ∧ 0 ≤ C ∧ 0 ≤ M ∧ 0 ≤ A ∧
      ∀ (x T : ℝ), 1 < x → 0 < T →
        |Arithmetic.logWeightedMangoldtSum x - x| ≤
          C * x ^ (1 - c / Real.log (T + 2) ^ 2) +
          M * x * T ^ (-(1 : ℝ) / 2) + A * (1 + Real.log x) := by
  obtain ⟨c, hc, hg⟩ := exists_zero_gap_all_heights
  refine ⟨c, (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight 2 ρ),
    (∑' ρ : ℂ, RiemannXi.inversePowerZeroWeight (3 / 2) ρ),
    (‖RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero‖ +
      |Real.log (2 * Real.pi)| + Real.pi ^ 2 / 24), hc,
    tsum_nonneg (RiemannXi.inversePowerZeroWeight_nonneg 2),
    tsum_nonneg (RiemannXi.inversePowerZeroWeight_nonneg (3 / 2)),
    add_nonneg (add_nonneg (norm_nonneg _) (abs_nonneg _))
      (div_nonneg (sq_nonneg _) (by norm_num only)), ?_⟩
  intro x T hx hT
  have h := logWeighted_main_error_le hc hg hx hT
  convert h using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
