/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FinitePointAvoidance
public import PseudoPrime.AnalyticNumberTheory.General.NearbyZeroExpansion

/-!
# Zero-avoiding heights for general entire completions

Local multiplicity counts select heights with a quantitative distance from every
zero ordinate, without a Riemann hypothesis or zeta-specific assumptions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- An entire function nonzero at zero has finite analytic order at every
point. The identity theorem on the plane rules out a locally zero function.
This ensures that every zero has a genuine positive natural multiplicity. -/
theorem entire_analyticOrderAt_ne_top {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (ρ : ℂ) :
    analyticOrderAt F ρ ≠ ⊤ := by
  intro ht
  have ha : AnalyticOnNhd ℂ F Set.univ := fun z _ ↦ hF.analyticAt z
  have he :=
    ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ ρ)
      (analyticOrderAt_eq_top.mp ht)
  exact h0 (he (Set.mem_univ 0))

/-- Every zero of an entire function nonzero at zero has positive natural
analytic multiplicity. Analyticity excludes order zero, and the identity
theorem excludes infinite order. This compares distinct zeros with their
multiplicity-weighted local count. -/
theorem entire_zero_multiplicity_pos {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {ρ : ℂ}
    (hz : F ρ = 0) : 0 < analyticOrderNatAt F ρ := by
  apply Nat.pos_of_ne_zero
  intro hn
  have he := ENat.toNat_eq_zero.mp hn
  rcases he with he | he
  · exact ((hF.analyticAt ρ).analyticOrderAt_ne_zero.mpr hz) he
  · exact entire_analyticOrderAt_ne_top hF h0 ρ he

/-- A critical-strip location within height distance two of H has norm at
most abs(H)+3. Bound its real and imaginary parts and use the complex norm
triangle bound. This places the height window in a compact disk. -/
theorem norm_zero_in_heightWindow_le {ρ : ℂ} {H : ℝ} (hlo : 0 ≤ ρ.re) (hhi : ρ.re ≤ 1)
    (hnear : |H - ρ.im| ≤ 2) : ‖ρ‖ ≤ |H| + 3 := by
  have hr : |ρ.re| ≤ 1 := by
    rw [abs_of_nonneg hlo]; exact hhi
  have hi : |ρ.im| ≤ |H| + 2 := by
    have hh := norm_add_le (ρ.im - H) H
    simp only [Real.norm_eq_abs] at hh
    rw [sub_add_cancel, abs_sub_comm] at hh
    linarith only [hh, hnear]
  have hn := Complex.norm_le_abs_re_add_abs_im ρ
  linarith only [hr, hi, hn]

/-- The zeros of an entire function nonzero at zero, confined to the
critical strip, form a finite set within height distance two of H. Embed the
window in a compact disk and use isolated-zero finiteness. This supplies the
finite forbidden-point ledger for height selection. -/
theorem finite_zero_heightWindow {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) (H : ℝ) :
    {ρ : ℂ | F ρ = 0 ∧ |H - ρ.im| ≤ 2}.Finite := by
  apply
    (finite_entire_zerosOn_compact hF h0
        (isCompact_closedBall (x := (0 : ℂ)) (r := |H| + 3))).subset
  intro ρ hρ
  refine ⟨?_, hρ.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_zero_in_heightWindow_le (hstrip ρ hρ.1).1 (hstrip ρ hρ.1).2 hρ.2

/-- A point within height distance two of H contributes its multiplicity
to at least one of the unit windows centered at H-1 and H+1. Split at height H;
the other local count is nonnegative. This bounds the wider window by the
two previously estimated local counts. -/
theorem multiplicity_le_two_localWindows (F : ℂ → ℂ) {H : ℝ} {ρ : ℂ} (hnear : |H - ρ.im| ≤ 2) :
    (analyticOrderNatAt F ρ : ℝ) ≤
      localZeroMultiplicity F (H - 1) ρ + localZeroMultiplicity F (H + 1) ρ := by
  classical
  have hh := abs_le.mp hnear
  by_cases hl : ρ.im ≤ H
  · have hn : |H - 1 - ρ.im| ≤ 1 := abs_le.mpr ⟨by linarith only [hl], by linarith only [hh.2]⟩
    rw [localZeroMultiplicity, ite_eq_left hn]
    exact le_add_of_nonneg_right (localZeroMultiplicity_nonneg F (H + 1) ρ)
  · have hn : |H + 1 - ρ.im| ≤ 1 :=
      abs_le.mpr ⟨by linarith only [hh.1], by linarith only [lt_of_not_ge hl]⟩
    rw [show localZeroMultiplicity F (H + 1) ρ = (analyticOrderNatAt F ρ : ℝ) from by
        simp only [localZeroMultiplicity, ite_eq_left hn]]
    exact le_add_of_nonneg_left (localZeroMultiplicity_nonneg F (H - 1) ρ)

/-- For finitely many actual zeros within height distance two of H, their
cardinality is bounded by the sum of the convergent local multiplicity counts
at H-1 and H+1. Positive orders dominate cardinality, and the two windows
dominate multiplicity. This controls the number of forbidden ordinates. -/
theorem card_zero_window_le_two_localCounts {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    (H : ℝ) (U : Finset ℂ) (hU : ∀ ρ ∈ U, F ρ = 0 ∧ |H - ρ.im| ≤ 2)
    (hminus : Summable (localZeroMultiplicity F (H - 1)))
    (hplus : Summable (localZeroMultiplicity F (H + 1))) :
    (U.card : ℝ) ≤
      (∑' ρ : ℂ, localZeroMultiplicity F (H - 1) ρ) +
        ∑' ρ : ℂ, localZeroMultiplicity F (H + 1) ρ := by
  have hp : ∀ ρ ∈ U, (1 : ℝ) ≤ (analyticOrderNatAt F ρ : ℝ) := by
    intro ρ hρ
    exact Nat.one_le_cast.mpr (entire_zero_multiplicity_pos hF h0 (hU ρ hρ).1)
  have hh := Finset.sum_le_sum hp
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  have hb := Finset.sum_le_sum (fun ρ hρ ↦ multiplicity_le_two_localWindows F (hU ρ hρ).2)
  rw [Finset.sum_add_distrib] at hb
  have hl := hminus.sum_le_tsum U (fun ρ _ ↦ localZeroMultiplicity_nonneg F (H - 1) ρ)
  have hr := hplus.sum_le_tsum U (fun ρ _ ↦ localZeroMultiplicity_nonneg F (H + 1) ρ)
  linarith only [hh, hb, hl, hr]

/-- Entire critical-strip zero data and summable local counts at H-1 and
H+1 yield a height T in [H,H+1] separated from every zero ordinate by the
reciprocal of four times one plus those counts. Apply finite interval avoidance
to the wider zero window; ordinates outside it are already at distance at
least one. This gives an explicit margin for horizontal contour edges. -/
theorem exists_height_avoiding_zeros_of_localCounts {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) (hstrip : ∀ ρ, F ρ = 0 → 0 ≤ ρ.re ∧ ρ.re ≤ 1) (H : ℝ)
    (hminus : Summable (localZeroMultiplicity F (H - 1)))
    (hplus : Summable (localZeroMultiplicity F (H + 1))) :
    ∃ T ∈ Set.Icc H (H + 1),
      ∀ ρ : ℂ,
        F ρ = 0 →
          1 /
              (4 *
                (1 + (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) +
                  ∑' z : ℂ, localZeroMultiplicity F (H + 1) z)) ≤
            |T - ρ.im| := by
  classical
  let U := (finite_zero_heightWindow hF h0 hstrip H).toFinset
  have hU : ∀ ρ ∈ U, F ρ = 0 ∧ |H - ρ.im| ≤ 2 := fun ρ hρ ↦ by
    simpa only [U, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hρ
  let S := U.image Complex.im
  let M : ℝ :=
    (∑' ρ : ℂ, localZeroMultiplicity F (H - 1) ρ) + ∑' ρ : ℂ, localZeroMultiplicity F (H + 1) ρ
  have hcard : (S.card : ℝ) ≤ M := by
    have hc : (S.card : ℝ) ≤ (U.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_image_le (s := U) (f := Complex.im))
    exact hc.trans (card_zero_window_le_two_localCounts hF h0 H U hU hminus hplus)
  have hM : 0 ≤ M := (Nat.cast_nonneg S.card).trans hcard
  let c : ℝ := 1 / (4 * (1 + M))
  have hden : 0 < 4 * (1 + M) := by linarith only [hM]
  have hc : 0 < c := div_pos zero_lt_one hden
  have hc1 : c ≤ 1 := by
    change 1 / (4 * (1 + M)) ≤ 1
    rw [div_le_iff₀ hden]
    linarith only [hM]
  have hlen : 2 * c * S.card < 1 := by
    change 2 * (1 / (4 * (1 + M))) * S.card < 1
    rw [← mul_div_assoc, div_mul_eq_mul_div, mul_one, div_lt_iff₀ hden]
    linarith only [hcard, hM]
  obtain ⟨T, hT, havoid⟩ := Analysis.exists_avoiding_point (a := H) hc hlen
  refine ⟨T, hT, ?_⟩
  intro ρ hz
  rw [add_assoc]
  change c ≤ |T - ρ.im|
  by_cases hn : |H - ρ.im| ≤ 2
  · exact
      havoid _
        (Finset.mem_image.mpr
          ⟨ρ, by
            simp only [U, Set.Finite.mem_toFinset]
            exact ⟨hz, hn⟩, rfl⟩)
  · have hHT : |H - T| ≤ 1 := abs_le.mpr ⟨by linarith only [hT.2], by linarith only [hT.1]⟩
    have hh := norm_add_le (H - T) (T - ρ.im)
    simp only [Real.norm_eq_abs, sub_add_sub_cancel] at hh
    have hfar : 1 < |T - ρ.im| := by linarith only [hh, hHT, lt_of_not_ge hn]
    exact hc1.trans hfar.le

/-- An entire order-one regularized completion with its functional equation
and right half-plane nonvanishing admits a height in each unit interval
separated from all zero ordinates by an explicit reciprocal local-count margin.
The functional equation supplies the strip and the reflected resolvent estimate
supplies summability. This removes separate window and convergence premises
from general explicit-formula height selection. -/
theorem exists_height_avoiding_zeros_of_orderAtMostOne {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (H : ℝ) :
    ∃ T ∈ Set.Icc H (H + 1),
      ∀ ρ : ℂ,
        F ρ = 0 →
          1 /
              (4 *
                (1 + (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) +
                  ∑' z : ℂ, localZeroMultiplicity F (H + 1) z)) ≤
            |T - ρ.im| := by
  exact
    exists_height_avoiding_zeros_of_localCounts hF h0
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) H
      (localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder (H - 1)).1
      (localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder (H + 1)).1

end PseudoPrime.AnalyticNumberTheory.General
