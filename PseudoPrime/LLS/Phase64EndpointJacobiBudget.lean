/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrincipalExponentialTailBounds
public import PseudoPrime.LLS.Phase64NumericalJacobiBudget

/-! # Finite analytic endpoint conditions for first-cell Jacobi witnesses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For the first level cell, finite endpoint and tail bounds give C/(407/10)
below the actual principal-ramp difference. Apply endpoint monotonicity with the certified
scale interval and root upper bound. -/
theorem phase64_principalRamp_lower_of_finite_bounds {L r p e C : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000) (N : ℕ)
    (hr : r ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (163840 / 99))
    (hp :
      (∑ n ∈ Finset.range N,
          Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
        p)
    (he : principalExponentialTailBound (4096128001 / 2475000) N ≤ e) (hC : C ≤ 2 * r - p - e)
    (hC0 : 0 ≤ C) : C / (407 / 10) ≤ principalRampDifference (L ^ 2 / (99 / 40)) := by
  have hx := Analysis.scale64_cell_of_level hlo hhi
  have hs : Real.sqrt (4096128001 / 2475000 : ℝ) ≤ 407 / 10 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  exact
    principalRampDifference_lower_of_finite_endpoints (by norm_num only : (0 : ℝ) < 163840 / 99)
      hx.1 hx.2 N hr hp he hC hC0 hs

/-- Under GRH and first-cell conductor hypotheses, finite endpoint estimates
and a strict explicit budget gap give an odd-prime negative Jacobi witness through L^2.
Apply the generic endpoint lower bound to the actual witness criterion. -/
theorem exists_odd_prime_negative_of_phase64_finite_endpoints {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L r p e C : ℝ}
    (hlo : 64 ≤ L) (hhi : L ≤ 64001 / 1000) (N : ℕ)
    (hr : r ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (163840 / 99))
    (hp :
      (∑ k ∈ Finset.range N,
          Real.exp (-(k : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt k) ≤
        p)
    (he : principalExponentialTailBound (4096128001 / 2475000) N ≤ e) (hC : C ≤ 2 * r - p - e)
    (hC0 : 0 ≤ C) (hgap : phase64NumericalJacobiBudget n q (L ^ 2 / (99 / 40)) < C / (407 / 10)) :
    ∃ k : ℕ, k.Prime ∧ Odd k ∧ (k : ℝ) ≤ L ^ 2 ∧ jacobiSym n k = -1 := by
  have hA := phase64_principalRamp_lower_of_finite_bounds hlo hhi N hr hp he hC hC0
  exact
    exists_odd_prime_negative_of_phase64_numerical_gap bridge hGRH hq hmq hlo hhi (hgap.trans_le hA)

/-- For the first cell, positive n, log(n)<=L and log(q)<=L+7/5, the explicit
Jacobi budget is strictly below 1373/(407/10). Bound the root below, certify the rational
negative power and compare rational caps. This removes the scalar budget-gap premise. -/
theorem phase64_numerical_budget_lt_endpoint_margin {n q : ℕ} (hn : 0 < n) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000) (hnL : Real.log n ≤ L) (hqL : Real.log q ≤ L + 7 / 5) :
    phase64NumericalJacobiBudget n q (L ^ 2 / (99 / 40)) < 1373 / (407 / 10) := by
  let x := L ^ 2 / (99 / 40)
  have hx := Analysis.scale64_cell_of_level hlo hhi
  have hx0 : (0 : ℝ) < x := (by norm_num only : (0 : ℝ) < 163840 / 99).trans_le hx.1
  have hs : (2034 / 50 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) hx0.le).mpr
      ((by norm_num only : (2034 / 50 : ℝ) ^ 2 ≤ 163840 / 99).trans hx.1)
  have hpcheck : (1 : ℚ) ≤ (7 / 430 : ℚ) ^ 16 * (163840 / 99 : ℚ) ^ 9 := by decide +kernel
  have hp :=
    (Analysis.rpow_neg_div_nat_interval (by norm_num only : (0 : ℝ) < 163840 / 99)
        (by norm_num only : (0 : ℝ) ≤ 0) (by norm_num only : (0 : ℝ) ≤ 7 / 430) 9 16
        (by norm_num only) (by norm_num only)
        (by
          have hc := (Rat.cast_le (K := ℝ)).mpr hpcheck
          simpa only [Rat.cast_one, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
            hc)).2
  have hxp :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 163840 / 99) hx.1
          (by norm_num only : (-9 / 16 : ℝ) ≤ 0)).trans
      hp
  have h4 : Real.log (4 : ℝ) ≤ 7 / 5 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hnlog : Real.log (4 * (n : ℝ)) ≤ L + 7 / 5 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hn).ne']
    linarith only [hnL, h4]
  have hlead := mul_le_mul_of_nonneg_left hnlog (by norm_num only : (0 : ℝ) ≤ 90992831 / 200000000)
  have hlin := mul_le_mul_of_nonneg_left hnL (by norm_num only : (0 : ℝ) ≤ 3 / 100)
  have hnum : (7 / 6 : ℝ) * Real.log q + 4 ≤ (7 / 6 : ℝ) * (64001 / 1000 + 7 / 5) + 4 := by
    linarith only [hqL, hhi]
  have hdiv :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ (7 / 6) * (64001 / 1000 + 7 / 5) + 4)
      (by norm_num only : (0 : ℝ) < 2034 / 50) hs
  have hpole := (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)).trans hdiv
  dsimp only [phase64NumericalJacobiBudget]
  change _ + _ - _ + _ + 43 * x ^ (-9 / 16 : ℝ) < _
  change x ^ (-9 / 16 : ℝ) ≤ 7 / 430 at hxp
  change (7 / 6 * Real.log q + 4) / Real.sqrt (L ^ 2 / (99 / 40)) ≤ _ at hpole
  nlinarith only [hlead, hlin, hpole, hxp, hhi]

/-- Under GRH, first-cell conductor and logarithm hypotheses, finite ramp cap
1514 and range-40000 principal cap 1654 give an odd-prime negative Jacobi witness through L^2.
The tail allowance 1/100 and scalar budget gap are proved. The two finite sum caps remain
inputs and are not certified numerical conclusions of this theorem. -/
theorem exists_odd_prime_negative_of_phase64_prefix_caps {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} (hq : 20000 ≤ q)
    (hmq : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ q) {L : ℝ} (hlo : 64 ≤ L)
    (hhi : L ≤ 64001 / 1000) (hnL : Real.log n ≤ L) (hqL : Real.log q ≤ L + 7 / 5)
    (hr : (1514 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum (163840 / 99))
    (hp :
      (∑ k ∈ Finset.range 40000,
          Real.exp (-(k : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt k) ≤
        (1654 : ℝ)) :
    ∃ k : ℕ, k.Prime ∧ Odd k ∧ (k : ℝ) ≤ L ^ 2 ∧ jacobiSym n k = -1 := by
  have he :=
    principalExponentialTailBound_40000_le (by norm_num only : (0 : ℝ) < 4096128001 / 2475000)
      (by norm_num only : (4096128001 / 2475000 : ℝ) ≤ 1660)
  exact
    exists_odd_prime_negative_of_phase64_finite_endpoints bridge hGRH hq hmq hlo hhi 40000 hr hp he
      (by norm_num only : (1373 : ℝ) ≤ 2 * 1514 - 1654 - 1 / 100)
      (by norm_num only : (0 : ℝ) ≤ 1373)
      (phase64_numerical_budget_lt_endpoint_margin hn.pos hlo hhi hnL hqL)

end PseudoPrime.LLS
