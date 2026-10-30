/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LocalZeroComparison
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.MainIntegral

/-!
# An unconditional squared-log zeta zero-free region

The nonnegative three-four-one Euler comparison, Jensen local factorization and the
real-axis pole residue give a zero-free strip at large absolute heights. The constants
and entrance height are existential; no prime-number-theorem error is assumed.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- As the real argument approaches one from above, the negative real zeta
logarithmic derivative is at most its simple pole plus the absolute Euler constant
and one. Use the established pole-cancellation limit. This preserves the leading
pole coefficient needed by the three-four-one zero-free argument. -/
theorem eventually_neg_re_logDeriv_le_pole :
    ∀ᶠ σ : ℝ in nhdsWithin 1 (Set.Ioi 1),
      -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + (|Real.eulerMascheroniConstant| + 1) := by
  have h :=
    tendsto_logDeriv_zeta_add_inv_sub_one.eventually
      (eventually_gt_nhds
        (show Real.eulerMascheroniConstant - 1 < Real.eulerMascheroniConstant by linarith only))
  filter_upwards [h] with σ hσ
  rw [← one_div] at hσ
  linarith only [hσ, neg_abs_le Real.eulerMascheroniConstant]

/-- For positive D, the real test point one plus the reciprocal of D times the
squared height logarithm tends to one from above. The logarithm tends to infinity
and the reciprocal tends to zero. This transfers the real pole estimate to large heights. -/
theorem tendsto_one_add_inv_log_sq {D : ℝ} (hD : 0 < D) :
    Filter.Tendsto (fun T : ℝ ↦ 1 + 1 / (D * Real.log (T + 2) ^ 2)) Filter.atTop
      (nhdsWithin 1 (Set.Ioi 1)) := by
  have hl :=
    Real.tendsto_log_atTop.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 Filter.tendsto_id)
  have hs := (Filter.tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by decide)).comp hl
  have hh := (hs.const_mul_atTop hD).inv_tendsto_atTop
  have ht :
    Filter.Tendsto (fun T : ℝ ↦ 1 + 1 / (D * Real.log (T + 2) ^ 2)) Filter.atTop (nhds 1) := by
    simpa only [Pi.inv_apply, one_div, Function.comp_apply, id_eq, add_zero] using hh.const_add 1
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨ht, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (8 : ℝ)] with T hT
  have hp : 0 < Real.log (T + 2) := Real.log_pos (by linarith only [hT])
  exact lt_add_of_pos_right 1 (one_div_pos.mpr (mul_pos hD (sq_pos_of_pos hp)))

/-- For a positive pole scale x, real part beta at most one, and remainder at most x/4,
the three-four-one reciprocal comparison forces beta at most one minus 1/(8*x).
Multiply by the positive distance and argue by contradiction. This extracts an explicit
zero gap from the local logarithmic-derivative budget. -/
theorem re_le_of_reciprocal_pole_budget {x E β : ℝ} (hx : 0 < x) (hβ : β ≤ 1) (hE : E ≤ x / 4)
    (hb : 4 / (1 + 1 / x - β) ≤ 3 * x + E) : β ≤ 1 - 1 / (8 * x) := by
  have hd : 0 < 1 + 1 / x - β := by
    have hi := one_div_pos.mpr hx
    linarith only [hβ, hi]
  have hp := (div_le_iff₀ hd).mp hb
  have hmul := mul_le_mul_of_nonneg_right hE hd.le
  have heq : x * (1 + 1 / x - β) = 1 + x * (1 - β) := by
    field_simp (disch := exact hx.ne')
    ring
  by_contra h
  have hbt : 1 - 1 / (8 * x) < β := lt_of_not_ge h
  have hbdiv : 1 - β < 1 / (8 * x) := by linarith only [hbt]
  have hbprod := (lt_div_iff₀ (show 0 < 8 * x by positivity)).mp hbdiv
  nlinarith only [hp, hmul, heq, hbprod]

/-- At heights at least eight, the squared logarithm at twice the height is at most
four times the squared height logarithm. Use logarithmic monotonicity and the product
identity. This combines the two local remainder costs into one squared-log scale. -/
theorem log_double_height_sq_le {T : ℝ} (hT : 8 ≤ T) :
    Real.log (2 * T + 2) ^ 2 ≤ 4 * Real.log (T + 2) ^ 2 := by
  have hp : 0 < T + 2 := by linarith only [hT]
  have ha : 0 ≤ Real.log (2 * T + 2) := Real.log_nonneg (by linarith only [hT])
  have hb : Real.log (2 * T + 2) ≤ 2 * Real.log (T + 2) := by
    have h1 :=
      Real.log_le_log (show 0 < 2 * T + 2 by linarith only [hT])
        (show 2 * T + 2 ≤ 2 * (T + 2) by linarith only)
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hp.ne'] at h1
    have h2 :=
      Real.log_le_log (show (0 : ℝ) < 2 by norm_num only) (show 2 ≤ T + 2 by linarith only [hT])
    linarith only [h1, h2]
  nlinarith only [ha, hb, sq_nonneg (2 * Real.log (T + 2) - Real.log (2 * T + 2))]

/-- There is a scale D at least one such that all zeta zeros of nonnegative real part
at every sufficiently large positive height have real part at most one minus
1/(8*D*log(T+2)^2). Choose D from the existing Jensen constant and the real pole remainder,
then evaluate the local zero comparison at one plus 1/(D*log(T+2)^2).
This proves the high-height gap without RH or an assumed prime-number-theorem error. -/
theorem eventually_zero_re_le_log_sq :
    ∃ D : ℝ,
      1 ≤ D ∧
        ∀ᶠ T : ℝ in Filter.atTop,
          ∀ ρ : ℂ,
            riemannZeta ρ = 0 →
              0 ≤ ρ.re → ρ.im = T → ρ.re ≤ 1 - 1 / (8 * D * Real.log (T + 2) ^ 2) := by
  let B : ℝ := |Real.eulerMascheroniConstant| + 1
  let K : ℝ := qMinusOneZetaLogDerivConst
  let D : ℝ := 32 * K + 12 * B + 1
  have hB : 0 ≤ B := by
    dsimp only [B]; positivity
  have hK : 0 ≤ K := qMinusOneZetaLogDerivConst_nonneg
  have hD : 0 < D := by
    dsimp only [D]; linarith only [hK, hB]
  have hD1 : 1 ≤ D := by
    dsimp only [D]; linarith only [hK, hB]
  refine ⟨D, hD1, ?_⟩
  have hr := (tendsto_one_add_inv_log_sq hD).eventually eventually_neg_re_logDeriv_le_pole
  filter_upwards [hr, Filter.eventually_ge_atTop (8 : ℝ)] with T hr hT
  intro ρ hρ hρ0 him
  let L : ℝ := Real.log (T + 2)
  have hL : 1 ≤ L := by
    apply (Real.le_log_iff_exp_le (show 0 < T + 2 by linarith only [hT])).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith only [hT])
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hx : 0 < D * L ^ 2 := mul_pos hD (lt_of_lt_of_le zero_lt_one hL2)
  have hx1 : 1 ≤ D * L ^ 2 := by
    nlinarith only [hD1, hL2, mul_nonneg (sub_nonneg.mpr hD1) (sub_nonneg.mpr hL2)]
  have hσ : 1 < 1 + 1 / (D * L ^ 2) := lt_add_of_pos_right 1 (one_div_pos.mpr hx)
  have hσ2 : 1 + 1 / (D * L ^ 2) ≤ 2 := by
    have h := one_div_le_one_div_of_le zero_lt_one hx1
    norm_num only [div_one] at h
    linarith only [h]
  have hp := zero_pole_le_logDeriv_budget hT hσ hσ2 hρ hρ0 him
  have hdouble := mul_le_mul_of_nonneg_left (log_double_height_sq_le hT) hK
  have hbudget : 4 / (1 + 1 / (D * L ^ 2) - ρ.re) ≤ 3 * (D * L ^ 2) + (3 * B + 8 * K * L ^ 2) := by
    change
      -(logDeriv riemannZeta ((1 + 1 / (D * L ^ 2) : ℝ) : ℂ)).re ≤
        1 / (1 + 1 / (D * L ^ 2) - 1) + B at hr
    rw [add_sub_cancel_left, one_div_one_div] at hr
    change
      4 / (1 + 1 / (D * L ^ 2) - ρ.re) ≤
        -3 * (logDeriv riemannZeta ((1 + 1 / (D * L ^ 2) : ℝ) : ℂ)).re + 4 * K * L ^ 2 +
          K * Real.log (2 * T + 2) ^ 2 at hp
    change K * Real.log (2 * T + 2) ^ 2 ≤ K * (4 * L ^ 2) at hdouble
    linarith only [hp, hr, hdouble]
  have hE : 3 * B + 8 * K * L ^ 2 ≤ (D * L ^ 2) / 4 := by
    have hBmul := mul_le_mul_of_nonneg_left hL2 hB
    dsimp only [D]
    nlinarith only [hBmul, hL2]
  have hg := re_le_of_reciprocal_pole_budget hx (re_zero_le_one hρ) hE hbudget
  convert hg using 1
  ring

/-- There are positive strip width and a height threshold at least eight such that
every actual zeta zero above that absolute height lies to the left of the squared-log
strip boundary. Conjugation handles negative heights; zeros of negative real part
satisfy the bound directly. This removes the sign and real-part restrictions of the
intermediate zero estimate. -/
theorem exists_zero_re_le_log_sq :
    ∃ (c T0 : ℝ),
      0 < c ∧
        8 ≤ T0 ∧
        ∀ ρ : ℂ, riemannZeta ρ = 0 → T0 ≤ |ρ.im| → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 2) ^ 2 := by
  obtain ⟨D, hD1, hevent⟩ := eventually_zero_re_le_log_sq
  obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.mp hevent
  have hD : 0 < D := zero_lt_one.trans_le hD1
  refine ⟨1 / (8 * D), max T1 8, by positivity, le_max_right _ _, ?_⟩
  intro ρ hρ hT
  have hT8 : 8 ≤ |ρ.im| := (le_max_right T1 8).trans hT
  have hTbig : T1 ≤ |ρ.im| := (le_max_left T1 8).trans hT
  have heq :
    (1 / (8 * D)) / Real.log (|ρ.im| + 2) ^ 2 = 1 / (8 * D * Real.log (|ρ.im| + 2) ^ 2) := by ring
  rw [heq]
  by_cases hρ0 : 0 ≤ ρ.re
  · by_cases hi : 0 ≤ ρ.im
    · have h := hT1 |ρ.im| hTbig ρ hρ hρ0 (abs_of_nonneg hi).symm
      exact h
    · have hin : ρ.im ≤ 0 := le_of_not_ge hi
      have hcz : riemannZeta (starRingEnd ℂ ρ) = 0 := by rw [riemannZeta_conj, hρ, map_zero]
      have h :=
        hT1 |ρ.im| hTbig (starRingEnd ℂ ρ) hcz (by simpa only [Complex.conj_re] using hρ0)
          (by rw [Complex.conj_im, abs_of_nonpos hin])
      simpa only [Complex.conj_re] using h
  · have hneg : ρ.re ≤ 0 := le_of_not_ge hρ0
    have hL : 1 ≤ Real.log (|ρ.im| + 2) := by
      apply (Real.le_log_iff_exp_le (show 0 < |ρ.im| + 2 by linarith only [hT8])).mpr
      exact Real.exp_one_lt_three.le.trans (by linarith only [hT8])
    have hL2 : 1 ≤ Real.log (|ρ.im| + 2) ^ 2 := one_le_pow₀ hL
    have hx1 : 1 ≤ D * Real.log (|ρ.im| + 2) ^ 2 := by
      nlinarith only [hD1, hL2, mul_nonneg (sub_nonneg.mpr hD1) (sub_nonneg.mpr hL2)]
    have hden : 1 ≤ 8 * D * Real.log (|ρ.im| + 2) ^ 2 := by nlinarith only [hx1]
    have hdiv := one_div_le_one_div_of_le zero_lt_one hden
    norm_num only [div_one] at hdiv
    linarith only [hneg, hdiv]

/-- There are positive squared-log strip width and a finite height threshold such that
zeta is nonzero strictly to the right of the strip boundary at both signs of large height.
Apply the zero real-part estimate to a hypothetical zero. This is an unconditional
zero-free-region input for a subsequent quantitative prime-number-theorem argument. -/
theorem exists_zeroFree_log_sq :
    ∃ (c T0 : ℝ),
      0 < c ∧
        8 ≤ T0 ∧
        ∀ s : ℂ, T0 ≤ |s.im| → 1 - c / Real.log (|s.im| + 2) ^ 2 < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨c, T0, hc, hT0, hz⟩ := exists_zero_re_le_log_sq
  exact ⟨c, T0, hc, hT0, fun s hs hr he ↦ (not_lt_of_ge (hz s he hs)) hr⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
