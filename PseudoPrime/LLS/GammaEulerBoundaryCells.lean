/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFiniteCenterScalarCertificate
public import PseudoPrime.LLS.GammaEulerSeedBoundaryBounds

/-! # Uniform signed target-boundary bounds from endpoint node certificates -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: validated rational node intervals at lo,hi and lo<=b<=hi.
Claim: node powers at b lie between the lower hi and upper lo endpoints.
Proof: negative real-power monotonicity. Role: reuse endpoint certificates on whole cells. -/
theorem gamma_node_power_bounds_on_cell {lo hi : ℚ} {rlo rhi : ℚ → ℚ × ℚ}
    (hl : Analysis.gammaFiniteEulerRatioCheck lo rlo = true)
    (hh : Analysis.gammaFiniteEulerRatioCheck hi rhi = true) {b : ℝ} (hlo : (lo : ℝ) ≤ b)
    (hhi : b ≤ (hi : ℝ)) (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    ((rhi ab.1).1 : ℝ) ≤ b ^ (-(1 / 2 + (ab.1 : ℝ))) ∧
      b ^ (-(1 / 2 + (ab.1 : ℝ))) ≤ ((rlo ab.1).2 : ℝ) := by
  have hpositive := (of_decide_eq_true hl).1
  have hlo0 : 0 < (lo : ℝ) := (Rat.cast_pos (K := ℝ)).mpr hpositive
  have hb0 := hlo0.trans_le hlo
  have he : -(1 / 2 + (ab.1 : ℝ)) ≤ 0 := by
    linarith only [gammaResolvent_real_exponents_gt_one ab hab]
  have h1 := (Analysis.gamma_finite_ratio_check_sound hh ab hab).1
  have h2 := (Analysis.gamma_finite_ratio_check_sound hl ab hab).2
  exact
    ⟨h1.trans (Real.rpow_le_rpow_of_nonpos hb0 hhi he),
      (Real.rpow_le_rpow_of_nonpos hlo0 hlo he).trans h2⟩

/-- Input: the same node cell and any rational node coefficient function.
Claim: the actual signed weighted sum lies between the endpoint-selected rational bounds.
Proof: preserve coefficient signs before summing. Role: enclose slopes and main tails. -/
theorem gamma_finite_weighted_bounds_on_cell {lo hi : ℚ} {rlo rhi : ℚ → ℚ × ℚ}
    (hl : Analysis.gammaFiniteEulerRatioCheck lo rlo = true)
    (hh : Analysis.gammaFiniteEulerRatioCheck hi rhi = true) {b : ℝ} (hlo : (lo : ℝ) ≤ b)
    (hhi : b ≤ (hi : ℝ)) (w : ℚ × ℚ → ℚ) :
    (gammaFiniteWeightedLower w (fun a ↦ ((rhi a).1, (rlo a).2)) : ℝ) ≤
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦ (w ab : ℝ) * b ^ (-(1 / 2 + (ab.1 : ℝ))))).sum ∧
      (Analysis.gammaResolventCoefficients.map
            (fun ab ↦ (w ab : ℝ) * b ^ (-(1 / 2 + (ab.1 : ℝ))))).sum ≤
        (gammaFiniteWeightedUpper w (fun a ↦ ((rhi a).1, (rlo a).2)) : ℝ) := by
  have hlower :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦
        (Analysis.signed_rational_node_bounds (b := w ab)
            (gamma_node_power_bounds_on_cell hl hh hlo hhi ab hab).1
            (gamma_node_power_bounds_on_cell hl hh hlo hhi ab hab).2).1)
  have hupper :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦
        (Analysis.signed_rational_node_bounds (b := w ab)
            (gamma_node_power_bounds_on_cell hl hh hlo hhi ab hab).1
            (gamma_node_power_bounds_on_cell hl hh hlo hhi ab hab).2).2)
  norm_num only [gammaFiniteWeightedLower, gammaFiniteWeightedUpper, Rat.cast_list_sum,
    List.map_map, Function.comp_def] at hlower hupper ⊢
  exact ⟨hlower, hupper⟩

/-- Input: any positive real cutoff b. Claim: the main tail is b times a fixed weighted
Euler power sum. Proof: factor one real cutoff power in the exact tail formula.
Role: extend rational-cutoff main-tail certificates to every point in a real cell. -/
theorem gamma_tail_main_eq_real_weighted {b : ℝ} (hb : 0 < b) :
    gammaEulerTailMain b =
      b *
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (gammaTailRationalCoefficient 1 ab : ℝ) * b ^ (-(1 / 2 + (ab.1 : ℝ))))).sum := by
  dsimp only [gammaEulerTailMain, gammaRealPowerList]
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ab _
  dsimp only [Function.comp_def, gammaTailRationalCoefficient]
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one]
  rw [show (1 : ℝ) - (1 / 2 + (ab.1 : ℝ)) = -(1 / 2 + (ab.1 : ℝ)) + 1 by ring,
    Real.rpow_add_one hb.ne']
  ring

/-- Input: a validated node cell and a nonnegative upper main-core allowance.
Claim: the Euler weight, slope and main tail have simultaneous uniform cell bounds.
Proof: combine signed intervals and bound the outer cutoff by hi.
Role: supply the three scalar inputs to the actual boundary-tail comparison. -/
theorem gamma_boundary_scalar_bounds_on_cell {lo hi : ℚ} {rlo rhi : ℚ → ℚ × ℚ}
    (hl : Analysis.gammaFiniteEulerRatioCheck lo rlo = true)
    (hh : Analysis.gammaFiniteEulerRatioCheck hi rhi = true) {b : ℝ} (hlo : (lo : ℝ) ≤ b)
    (hhi : b ≤ (hi : ℝ))
    (hM :
      0 ≤
        gammaFiniteWeightedUpper (gammaTailRationalCoefficient 1)
          (fun a ↦ ((rhi a).1, (rlo a).2))) :
    (Analysis.gammaFiniteEulerLower (fun a ↦ ((rhi a).1, (rlo a).2)) : ℝ) ≤
        Analysis.gammaResolventEulerWeight b ∧
      gammaEulerLogSlope b ≤
        (gammaFiniteWeightedUpper gammaSlopeRationalCoefficient (fun a ↦ ((rhi a).1, (rlo a).2)) :
          ℝ) ∧
      gammaEulerTailMain b ≤
        (hi : ℝ) *
          (gammaFiniteWeightedUpper (gammaTailRationalCoefficient 1)
              (fun a ↦ ((rhi a).1, (rlo a).2)) :
            ℝ) := by
  have hnode := fun ab hab ↦ gamma_node_power_bounds_on_cell hl hh hlo hhi ab hab
  have hweight :=
    (Analysis.gamma_finite_euler_bounds (m := b) (fun a ↦ ((rhi a).1, (rlo a).2)) hnode).1
  have hslope :=
    (gamma_finite_weighted_bounds_on_cell hl hh hlo hhi gammaSlopeRationalCoefficient).2
  rw [← gamma_slope_eq_weighted] at hslope
  have hlo0 := (Rat.cast_pos (K := ℝ)).mpr (of_decide_eq_true hl).1
  have hb0 := hlo0.trans_le hlo
  have hmain :=
    (gamma_finite_weighted_bounds_on_cell hl hh hlo hhi (gammaTailRationalCoefficient 1)).2
  have hm :=
    (mul_le_mul_of_nonneg_left hmain hb0.le).trans
      (mul_le_mul_of_nonneg_right hhi ((Rat.cast_nonneg (K := ℝ)).mpr hM))
  rw [← gamma_tail_main_eq_real_weighted hb0] at hm
  exact ⟨hweight, hslope, hm⟩

/-- Input: RH and 1<=t<=300000. Claim: the smoothed Mangoldt error is at most 55.
Proof: bound the existing refined global error's root and logarithm terms.
Role: avoid finite prime-power arithmetic at the target boundary. -/
theorem gamma_smoothed_error_le_fifty_five (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t)
    (hT : t ≤ 300000) : |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤ 55 := by
  have he := logWeightedMangoldtSum_error_le_refined_global hRH (zero_lt_one.trans_le ht)
  rw [max_eq_right ht] at he
  have hs : Real.sqrt t ≤ 548 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num only, hT.trans (by norm_num only : (300000 : ℝ) ≤ 548 ^ 2)⟩
  have hl :=
    Real.log_le_log (zero_lt_one.trans_le ht) (hT.trans (by norm_num only : (300000 : ℝ) ≤ 2 ^ 19))
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [he, hs, hl, Real.log_two_lt_d9]

/-- Input: RH and 50000<=b<=300000. Claim: psi(b)>=(19/20)b-2090 and A(b)>=b-55.
Proof: compare smoothed sums at (19/20)b and b, using their uniform errors.
Role: provide analytic lower bounds for both negative boundary products. -/
theorem gamma_target_boundary_arithmetic_lower (hRH : RiemannHypothesis) {b : ℝ} (hb : 50000 ≤ b)
    (hB : b ≤ 300000) :
    (19 / 20 : ℝ) * b - 2090 ≤ Chebyshev.psi b ∧
      b - 55 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b := by
  have hb0 : 0 < b := by linarith only [hb]
  have hx0 : 0 < (19 / 20 : ℝ) * b := mul_pos (by norm_num only) hb0
  have hxy : (19 / 20 : ℝ) * b < b := by linarith only [hb0]
  have hx :=
    gamma_smoothed_error_le_fifty_five hRH (show (1 : ℝ) ≤ (19 / 20 : ℝ) * b by linarith only [hb])
      (show (19 / 20 : ℝ) * b ≤ 300000 by linarith only [hB, hb0])
  have hy := gamma_smoothed_error_le_fifty_five hRH (show (1 : ℝ) ≤ b by linarith only [hb]) hB
  have hp :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error_without_log hx0 hxy hx hy).2
  have heq : ((55 : ℝ) + 55) * ((19 / 20 : ℝ) * b) / (b - (19 / 20 : ℝ) * b) = 2090 := by
    apply (div_eq_iff (sub_pos.mpr hxy).ne').mpr
    ring
  rw [heq] at hp
  exact ⟨hp, by linarith only [(abs_le.mp hy).1]⟩

end PseudoPrime.LLS
