/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseScalar656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTail644

/-! # Inverse-square tail of the section 132 zero-phase sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem phase_full_656 {s : ℂ} {L t : ℝ} (hL : 0 < L) (ht : L ≤ |t|) (hs : |t| ≤ ‖s‖) :
    ‖(11 / 10 : ℂ) ^ 5 * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) / s ^ 6‖ * |t| ^ 2 ≤
      (11 / 10 : ℝ) ^ 5 / L ^ 4 := by
  have hp : 0 < |t| := hL.trans_le ht
  have hden : |t| ^ 2 * L ^ 4 ≤ ‖s‖ ^ 6 := by
    rw [show (6 : ℕ) = 2 + 4 by decide, pow_add]
    exact
      mul_le_mul (pow_le_pow_left₀ hp.le hs 2) (pow_le_pow_left₀ hL.le (ht.trans hs) 4)
        (pow_nonneg hL.le _) (pow_nonneg (norm_nonneg _) _)
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_div, Complex.norm_ofNat, Complex.norm_ofNat,
    Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    Real.exp_zero, mul_one]
  calc
    _ ≤ ((11 / 10 : ℝ) ^ 5 / (|t| ^ 2 * L ^ 4)) * |t| ^ 2 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num only) (mul_pos (sq_pos_of_pos hp) (pow_pos hL _))
          hden)
        (sq_nonneg _)
    _ = _ := by field_simp [hp.ne', hL.ne']

/-- The rational inverse-square envelope at a positive lower ordinate.
The coefficient sum uses the derivative part and the Mellin part. -/
noncomputable def quarterPhaseBudget656 (L : ℝ) : ℝ :=
  (299100304093269000 / 10 ^ 20 : ℝ) * (∑ j ∈ Finset.range 6, |quarterPhaseCoeff656 j| / L ^ j) +
    (11 / 10 : ℝ) ^ 5 / L ^ 4

/-- For a positive lower ordinate, the scaled phase norm is bounded by
the explicit rational envelope. This applies to the high tail and to each
certified low bracket in the curvature computation. -/
theorem quarter_phase_norm_budget_656 {L t : ℝ} (hL : 0 < L) (ht : L ≤ |t|) :
    ‖quarterPhaseKernel656 t‖ * |t| ^ 2 ≤ quarterPhaseBudget656 L := by
  let s : ℂ := 11 / 10 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  let C : ℝ := (11 / 10) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  have hs : |t| ≤ ‖s‖ := by
    have he : s.im = t := by
      dsimp only [s]
      norm_num only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, zero_add, Complex.div_ofNat_im, Complex.im_ofNat]
    exact he ▸ Complex.abs_im_le_norm s
  have hw : |t| ≤ ‖w‖ := by
    have he : w.im = t := by
      dsimp only [w]
      norm_num only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, zero_add, Complex.div_ofNat_im, Complex.one_im]
    exact he ▸ Complex.abs_im_le_norm w
  have hC : 0 ≤ 4 * C := by
    dsimp only [C]; positivity
  let F := fun j : ℕ ↦ (quarterPhaseCoeff656 j : ℂ) / (w * s ^ (j + 1))
  let G := (11 / 10 : ℂ) ^ 5 * Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ)) / s ^ 6
  have h := norm_add_le (((4 * C : ℝ) : ℂ) * ∑ j ∈ Finset.range 6, F j) G
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC] at h
  have hF := (mul_le_mul_of_nonneg_right (norm_sum_le (Finset.range 6) F) (sq_nonneg |t|))
  rw [Finset.sum_mul] at hF
  have hT := hF.trans (Finset.sum_le_sum (fun j _ ↦ phase_reciprocal hL ht hs hw _ j))
  have hv := phase_full_656 hL ht hs
  have hc :=
    mul_le_mul_of_nonneg_right quarter_phase_normalization_656.2
      (show 0 ≤ ∑ j ∈ Finset.range 6, |quarterPhaseCoeff656 j| / L ^ j by positivity)
  change ‖((4 * C : ℝ) : ℂ) * (∑ j ∈ Finset.range 6, F j) + G‖ * |t| ^ 2 ≤ _
  unfold quarterPhaseBudget656
  change (4 * C) * _ ≤ _ at hc
  change ‖G‖ * |t| ^ 2 ≤ _ at hv
  nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg |t|), mul_le_mul_of_nonneg_left hT hC, hv,
    hc]

/-- For ordinates of absolute value at least 100, the section 132 phase
kernel has inverse-square decay with constant 0.51506148. -/
theorem quarter_phase_high_656 {t : ℝ} (ht : 100 ≤ |t|) :
    ‖quarterPhaseKernel656 t‖ ≤ 0.51506148 / |t| ^ 2 := by
  have hp : 0 < (100 : ℝ) := by norm_num only
  apply (le_div_iff₀ (sq_pos_of_pos (hp.trans_le ht))).mpr
  apply (quarter_phase_norm_budget_656 hp ht).trans
  norm_num only [quarterPhaseBudget656, Finset.sum_range_succ, Finset.sum_range_zero,
    quarterPhaseCoeff656, Nat.factorial, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, ite_true, ite_false, abs_of_nonneg, abs_of_nonpos]

/-- Under RH, any finite set of nontrivial zeros above absolute ordinate
100 contributes at most 0.006592787 to the phase mass, with multiplicities.
The retained count bounds the inverse-square ordinate tail. -/
theorem quarter_phase_tail_656 (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖quarterPhaseKernel656 ρ.im‖) ≤
      0.006592787 := by
  have h := AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S 100 hz hre ht
  have htail :=
    section104_ordinate_tail_le hRH (AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH)
  have hsum := mul_le_mul_of_nonneg_left (h.trans htail) (by norm_num only : (0 : ℝ) ≤ 0.51506148)
  rw [Finset.mul_sum] at hsum
  have hb : (0.51506148 : ℝ) * 0.0128 ≤ 0.006592787 := by norm_num only
  apply (Finset.sum_le_sum (fun ρ hρ ↦ ?_)).trans (hsum.trans hb)
  have hρ' := quarter_phase_high_656 (ht ρ hρ).le
  exact (mul_le_mul_of_nonneg_left hρ' (Nat.cast_nonneg _)).trans_eq (by ring)

/-- A real phase shift does not change the individual norms. The finite
high-zero phase sum is therefore bounded below by minus its tail budget. -/
theorem quarter_phase_tail_lower_656 (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|)
    (x : ℝ) :
    (-0.006592787 : ℝ) ≤
      ∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im).re := by
  have h := quarter_phase_tail_656 hRH S hz hre ht
  have hsum :
    -(∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ‖quarterPhaseKernel656 ρ.im‖) ≤
      ∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im).re := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hn : ‖Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
        Real.exp_zero]
    let w := Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im
    have hl : -‖w‖ ≤ w.re := (neg_le_neg (Complex.abs_re_le_norm w)).trans (neg_abs_le w.re)
    dsimp only [w] at hl
    rw [norm_mul, hn, one_mul] at hl
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
  linarith only [h, hsum]

/-- A lower bound on the low-ordinate part of a finite zero sum extends
to the whole sum after paying the section 132 high-ordinate budget. -/
theorem quarter_phase_finite_lower_656 (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (x B : ℝ) :
    let W := fun ρ : ℂ ↦
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
        (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel656 ρ.im).re
    B ≤ (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ 100), W ρ) → B - 0.006592787 ≤ ∑ ρ ∈ S, W ρ := by
  classical
  intro W hB
  let T := S.filter (fun ρ ↦ ¬|ρ.im| ≤ 100)
  have hT :=
    quarter_phase_tail_lower_656 hRH T (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2) x
  have hs := Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ |ρ.im| ≤ 100) W
  change (-0.006592787 : ℝ) ≤ ∑ ρ ∈ T, W ρ at hT
  change (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ 100), W ρ) + (∑ ρ ∈ T, W ρ) = _ at hs
  linarith only [hB, hT, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
