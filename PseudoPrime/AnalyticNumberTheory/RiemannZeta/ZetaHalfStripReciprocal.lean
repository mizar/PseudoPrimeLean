/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripBounds

/-! # Lower bound for zeta on the right half-plane -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `Re s ≥ 3/2`, the norm of the Möbius L-series is bounded by the
positive real Dirichlet series at `3/2`. Absolute convergence and the bound
`|μ(n)| ≤ 1` give the termwise comparison. -/
private theorem norm_moebius_le_series {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
      ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hs1 : 1 < s.re := by linarith only [hs]
  have hc : Summable (LSeries.term (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs1
  have hr : Summable (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num only))
  have hterm :
    Summable
      (fun n : ℕ ↦ ‖LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.moebius k : ℂ)) s (n + 1)‖) :=
    (summable_nat_add_iff 1).mpr hc.norm
  have hcmp :
    (∑' n : ℕ, ‖LSeries.term (fun k : ℕ ↦ (ArithmeticFunction.moebius k : ℂ)) s (n + 1)‖) ≤
      ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    apply hterm.tsum_le_tsum _ hr
    intro n
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), norm_div]
    have hmu : ‖(ArithmeticFunction.moebius (n + 1) : ℂ)‖ ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n + 1))
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ n
    have hb : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_succ n)]
    have hd : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ s.re) := Real.rpow_nonneg hn.le _
    have hfirst :
      ‖(ArithmeticFunction.moebius (n + 1) : ℂ)‖ / (((n + 1 : ℕ) : ℝ) ^ s.re) ≤
        1 / (((n + 1 : ℕ) : ℝ) ^ s.re) :=
      div_le_div_of_nonneg_right hmu hd
    have hsecond : 1 / (((n + 1 : ℕ) : ℝ) ^ s.re) ≤ (((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [one_div, ← Real.rpow_neg hn.le s.re]
      apply Real.rpow_le_rpow_of_exponent_le hb
      linarith only [hs]
    exact hfirst.trans hsecond
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hc.norm).trans ?_
  have hsum := hc.norm.tsum_eq_zero_add
  simp only [LSeries.term_zero, norm_zero, zero_add] at hsum
  rw [hsum]
  exact hcmp

/-- On `Re s ≥ 3/2`, the zeta norm is at least `5/14`. The Möbius
L-series is its reciprocal and is bounded by the real Dirichlet series,
whose elementary integral estimate is less than `14/5`. -/
theorem five_fourteenths_le_norm_zeta {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    (5 / 14 : ℝ) ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by linarith only [hs]
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num only)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num only)
  have hlow : (25 / 18 : ℝ) < Real.sqrt 2 := by nlinarith only [hs0, hs2]
  have hinv := one_div_lt_one_div_of_lt (by norm_num only : (0 : ℝ) < 25 / 18) hlow
  norm_num only [one_div] at hinv
  have hscalar : 1 + (5 / 2 : ℝ) * (Real.sqrt 2)⁻¹ ≤ 14 / 5 := by linarith only [hinv]
  have hb : ‖LSeries (fun n : ℕ ↦ (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ (14 / 5 : ℝ) :=
    (norm_moebius_le_series hs).trans (zeta_three_halves_series_le.trans hscalar)
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at hprod
  have hn := congrArg norm hprod
  rw [norm_mul, norm_one] at hn
  have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (riemannZeta s))
  nlinarith only [hn, hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
