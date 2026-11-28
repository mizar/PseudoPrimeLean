/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalZeros
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH

/-! # The fixed phase kernel and the high-zero envelope in section 122 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The differentiated unit-cutoff coefficients, indexed from zero.
At index j the coefficient multiplies the inverse power of degree j+1. -/
noncomputable def quarterPhaseCoeff644 (j : ℕ) : ℝ :=
  let c (k : ℕ) : ℝ := if k ≤ 5 then (120 / (5 - k).factorial) * (2687 / 1000) ^ (5 - k) else 0
  57 / 100 * c j - c (j + 1)

/-- The phase kernel in (122.28), with the critical-line ordinate t.
The first summand retains the derivative coefficients and the second
is the full Mellin term. -/
noncomputable def quarterPhaseKernel644 (t : ℝ) : ℂ :=
  let s : ℂ := 107 / 100 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  let C : ℝ := (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
  ((4 * C : ℝ) : ℂ) * (∑ j ∈ Finset.range 6, (quarterPhaseCoeff644 j : ℂ) / (w * s ^ (j + 1))) +
    ((107 / 100 : ℂ) ^ 5 * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ))) / s ^ 6

private theorem phase_reciprocal {s w : ℂ} {L T : ℝ} (hL : 0 < L) (hT : L ≤ T) (hs : T ≤ ‖s‖)
    (hw : T ≤ ‖w‖) (d : ℝ) (j : ℕ) : ‖(d : ℂ) / (w * s ^ (j + 1))‖ * T ^ 2 ≤ |d| / L ^ j := by
  have hpos : 0 < T := hL.trans_le hT
  have hLpow : 0 < L ^ j := pow_pos hL _
  have hden : T ^ 2 * L ^ j ≤ ‖w‖ * ‖s‖ ^ (j + 1) := by
    rw [pow_succ]
    calc
      _ = T * (L ^ j * T) := by ring
      _ ≤ _ :=
        mul_le_mul hw
          (mul_le_mul (pow_le_pow_left₀ hL.le (hT.trans hs) j) hs hpos.le
            (pow_nonneg (norm_nonneg _) _))
          (mul_nonneg hLpow.le hpos.le) (norm_nonneg _)
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (|d| / (T ^ 2 * L ^ j)) * T ^ 2 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (sq_pos_of_pos hpos) hLpow) hden)
        (sq_nonneg _)
    _ = _ := by field_simp [hpos.ne', hLpow.ne']

private theorem phase_full {s : ℂ} {L t : ℝ} (hL : 0 < L) (ht : L ≤ |t|) (hs : |t| ≤ ‖s‖) :
    ‖(107 / 100 : ℂ) ^ 5 * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) / s ^ 6‖ *
        |t| ^ 2 ≤
      (107 / 100 : ℝ) ^ 5 / L ^ 4 := by
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
    _ ≤ ((107 / 100 : ℝ) ^ 5 / (|t| ^ 2 * L ^ 4)) * |t| ^ 2 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by norm_num only) (mul_pos (sq_pos_of_pos hp) (pow_pos hL _))
          hden)
        (sq_nonneg _)
    _ = _ := by field_simp [hp.ne', hL.ne']

private theorem phase_constant_upper :
    ((107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120) ≤
      (107 / 100 : ℝ) ^ 5 * (56411062281 / 1000000000000) / 120 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 287509 / 100000) 26
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  have hi := one_div_le_one_div_of_le (by norm_num only) h
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  rw [show -(107 / 100 : ℝ) * (2687 / 1000) = -(287509 / 100000) by norm_num only]
  linarith only [hi]

/-- The rational inverse-square envelope at a positive lower ordinate.
The coefficient sum uses the derivative part and the Mellin part. -/
noncomputable def quarterPhaseBudget644 (L : ℝ) : ℝ :=
  4 * ((107 / 100 : ℝ) ^ 5 * (56411062281 / 1000000000000) / 120) *
      (∑ j ∈ Finset.range 6, |quarterPhaseCoeff644 j| / L ^ j) +
    (107 / 100 : ℝ) ^ 5 / L ^ 4

/-- For a positive lower ordinate, the scaled phase norm is bounded by
the explicit rational envelope. This applies to the high tail and to each
certified low bracket in the curvature computation. -/
theorem quarter_phase_norm_budget_644 {L t : ℝ} (hL : 0 < L) (ht : L ≤ |t|) :
    ‖quarterPhaseKernel644 t‖ * |t| ^ 2 ≤ quarterPhaseBudget644 L := by
  let s : ℂ := 107 / 100 + Complex.I * t
  let w : ℂ := 1 / 2 + Complex.I * t
  let C : ℝ := (107 / 100) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120
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
  let F := fun j : ℕ ↦ (quarterPhaseCoeff644 j : ℂ) / (w * s ^ (j + 1))
  let G := (107 / 100 : ℂ) ^ 5 * Complex.exp (Complex.I * ((2687 / 1000 : ℝ) * t : ℝ)) / s ^ 6
  have h := norm_add_le (((4 * C : ℝ) : ℂ) * ∑ j ∈ Finset.range 6, F j) G
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC] at h
  have hF := (mul_le_mul_of_nonneg_right (norm_sum_le (Finset.range 6) F) (sq_nonneg |t|))
  rw [Finset.sum_mul] at hF
  have hT := hF.trans (Finset.sum_le_sum (fun j _ ↦ phase_reciprocal hL ht hs hw _ j))
  have hv := phase_full hL ht hs
  have hc :=
    mul_le_mul_of_nonneg_right phase_constant_upper
      (show 0 ≤ ∑ j ∈ Finset.range 6, |quarterPhaseCoeff644 j| / L ^ j by positivity)
  change ‖((4 * C : ℝ) : ℂ) * (∑ j ∈ Finset.range 6, F j) + G‖ * |t| ^ 2 ≤ _
  unfold quarterPhaseBudget644
  change C * _ ≤ _ at hc
  change ‖G‖ * |t| ^ 2 ≤ _ at hv
  nlinarith only [mul_le_mul_of_nonneg_right h (sq_nonneg |t|), mul_le_mul_of_nonneg_left hT hC, hv,
    hc]

/-- For ordinates of absolute value at least 100, the section 122 phase
kernel has inverse-square decay with constant 0.484. -/
theorem quarter_phase_high_644 {t : ℝ} (ht : 100 ≤ |t|) :
    ‖quarterPhaseKernel644 t‖ ≤ 0.484 / |t| ^ 2 := by
  have hp : 0 < (100 : ℝ) := by norm_num only
  apply (le_div_iff₀ (sq_pos_of_pos (hp.trans_le ht))).mpr
  apply (quarter_phase_norm_budget_644 hp ht).trans
  norm_num only [quarterPhaseBudget644, Finset.sum_range_succ, Finset.sum_range_zero,
    quarterPhaseCoeff644, Nat.factorial, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, ite_true, ite_false, abs_of_nonneg, abs_of_nonpos]

/-- Under RH, any finite set of nontrivial zeros above absolute ordinate
100 contributes at most 0.0061952 to the phase mass, with multiplicities.
The retained count bounds the inverse-square ordinate tail. -/
theorem quarter_phase_tail_644 (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          ‖quarterPhaseKernel644 ρ.im‖) ≤
      0.0061952 := by
  have h := AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S 100 hz hre ht
  have htail :=
    section104_ordinate_tail_le hRH (AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH)
  have hsum := mul_le_mul_of_nonneg_left (h.trans htail) (by norm_num only : (0 : ℝ) ≤ 0.484)
  rw [Finset.mul_sum] at hsum
  have hb : (0.484 : ℝ) * 0.0128 ≤ 0.0061952 := by norm_num only
  apply (Finset.sum_le_sum (fun ρ hρ ↦ ?_)).trans (hsum.trans hb)
  have hρ' := quarter_phase_high_644 (ht ρ hρ).le
  exact (mul_le_mul_of_nonneg_left hρ' (Nat.cast_nonneg _)).trans_eq (by ring)

/-- A real phase shift does not change the individual norms. The finite
high-zero phase sum is therefore bounded below by minus its tail budget. -/
theorem quarter_phase_tail_lower_644 (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (ht : ∀ ρ ∈ S, 100 < |ρ.im|)
    (x : ℝ) :
    (-0.0061952 : ℝ) ≤
      ∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im).re := by
  have h := quarter_phase_tail_644 hRH S hz hre ht
  have hsum :
    -(∑ ρ ∈ S,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            ‖quarterPhaseKernel644 ρ.im‖) ≤
      ∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im).re := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hn : ‖Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
        Real.exp_zero]
    let w := Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im
    have hl : -‖w‖ ≤ w.re := (neg_le_neg (Complex.abs_re_le_norm w)).trans (neg_abs_le w.re)
    dsimp only [w] at hl
    rw [norm_mul, hn, one_mul] at hl
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
  linarith only [h, hsum]

/-- A lower bound on the low-ordinate part of a finite zero sum extends
to the whole sum after paying the section 122 high-ordinate budget. -/
theorem quarter_phase_finite_lower_644 (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (x B : ℝ) :
    let W := fun ρ : ℂ ↦
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
        (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) * quarterPhaseKernel644 ρ.im).re
    B ≤ (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ 100), W ρ) → B - 0.0061952 ≤ ∑ ρ ∈ S, W ρ := by
  classical
  intro W hB
  let T := S.filter (fun ρ ↦ ¬|ρ.im| ≤ 100)
  have hT :=
    quarter_phase_tail_lower_644 hRH T (fun ρ hρ ↦ hz ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ hre ρ (Finset.mem_filter.mp hρ).1)
      (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2) x
  have hs := Finset.sum_filter_add_sum_filter_not S (fun ρ ↦ |ρ.im| ≤ 100) W
  change (-0.0061952 : ℝ) ≤ ∑ ρ ∈ T, W ρ at hT
  change (∑ ρ ∈ S.filter (fun ρ ↦ |ρ.im| ≤ 100), W ρ) + (∑ ρ ∈ T, W ρ) = _ at hs
  linarith only [hB, hT, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
