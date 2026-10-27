/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import Mathlib.NumberTheory.Chebyshev

/-! # Explicit positive Euler weight and analytic prefix growth -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: an antitone weight on the resolvent nodes, nonnegative at seven.
Claim: the signed combination dominates half its leading node. Use positive
cumulative coefficients. Role: retain a quantitative part of Euler positivity. -/
theorem gammaResolvent_weighted_ge_half_leading (w : ℚ → ℝ) (hw : Antitone w) (hzero : 0 ≤ w 7) :
    (1 / 2 : ℝ) * w (11 / 20) ≤
      (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * w ab.1)).sum := by
  have h1 := hw (by norm_num only : (11 / 20 : ℚ) ≤ 16 / 20)
  have h2 := hw (by norm_num only : (16 / 20 : ℚ) ≤ 20 / 20)
  have h3 := hw (by norm_num only : (20 / 20 : ℚ) ≤ 34 / 20)
  have h4 := hw (by norm_num only : (34 / 20 : ℚ) ≤ 46 / 20)
  have h5 := hw (by norm_num only : (46 / 20 : ℚ) ≤ 64 / 20)
  have h6 := hw (by norm_num only : (64 / 20 : ℚ) ≤ 90 / 20)
  have h7 := hw (by norm_num only : (90 / 20 : ℚ) ≤ 140 / 20)
  norm_num only [gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at ⊢ h1 h2 h3 h4 h5 h6 h7
  linarith only [h1, h2, h3, h4, h5, h6, h7, hzero]

/-- Input: t>=1. Claim: the actual signed Euler weight is at least half t^(-21/20).
Apply the antitone-node comparison to the real powers.
Role: turn qualitative positivity into a prefix-growth lower bound. -/
theorem gamma_resolvent_euler_weight_ge_half_power {t : ℝ} (ht : 1 ≤ t) :
    (1 / 2 : ℝ) * t ^ (-21 / 20 : ℝ) ≤ gammaResolventEulerWeight t := by
  have hanti : Antitone (fun a : ℚ ↦ t ^ (-(1 / 2 + (a : ℝ)))) := by
    intro a b hab
    exact Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg (add_le_add le_rfl (Rat.cast_le.mpr hab)))
  have h :=
    gammaResolvent_weighted_ge_half_leading _ hanti (Real.rpow_nonneg (zero_le_one.trans ht) _)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [gammaResolventEulerWeight, neg_div] using h

/-- Input: ordered natural endpoints and a real-valued sequence. Claim: its
prefix splits over the two adjacent intervals. Use disjoint interval union.
Role: share the exact split for the Euler prefix and Chebyshev psi. -/
theorem gamma_prefix_split {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc 0 b, f n) = (∑ n ∈ Finset.Ioc 0 a, f n) + ∑ n ∈ Finset.Ioc a b, f n := by
  have hd : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a b) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hn).2) (Finset.mem_Ioc.mp hm).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab, Finset.sum_union hd]

/-- Input: ordered natural endpoints a<=b. Claim: the Euler interval sum is
at least half b^(-21/20) times psi(b)-psi(a). Compare every positive index
with the endpoint power. Role: retain a positive prime-power block analytically. -/
theorem gamma_euler_interval_lower_of_psi {a b : ℕ} (hab : a ≤ b) :
    (1 / 2 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * (Chebyshev.psi b - Chebyshev.psi a) ≤
      ∑ n ∈ Finset.Ioc a b, gammaResolventMangoldtWeight n := by
  have hp :
    Chebyshev.psi b - Chebyshev.psi a = ∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n := by
    simp only [Chebyshev.psi, Nat.floor_natCast]
    linarith only [gamma_prefix_split hab (fun n ↦ ArithmeticFunction.vonMangoldt n)]
  rw [hp, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le a) (Finset.mem_Ioc.mp hn).1
  have hnb : (n : ℝ) ≤ b := Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2
  have hpow :=
    Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hn0) hnb (by norm_num only : (-21 / 20 : ℝ) ≤ 0)
  have hl :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 1 / 2)).trans
      (gamma_resolvent_euler_weight_ge_half_power (Nat.one_le_cast.mpr hn0))
  simpa only [gammaResolventMangoldtWeight, mul_comm] using
    (mul_le_mul_of_nonneg_right hl (ArithmeticFunction.vonMangoldt_nonneg (n := n)))

/-- Input: a proved prefix lower bound at a and b>=a. Claim: it grows by
at least half b^(-21/20)(psi(b)-psi(a)). Split the prefix and add the interval
bound. Role: strengthen fixed prefix credits without new finite certificates. -/
theorem gamma_euler_prefix_lower_growth {a b : ℕ} {C : ℝ} (hab : a ≤ b)
    (hC : C ≤ ∑ n ∈ Finset.Ioc 0 a, gammaResolventMangoldtWeight n) :
    C + (1 / 2 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * (Chebyshev.psi b - Chebyshev.psi a) ≤
      ∑ n ∈ Finset.Ioc 0 b, gammaResolventMangoldtWeight n := by
  rw [gamma_prefix_split hab]
  exact add_le_add hC (gamma_euler_interval_lower_of_psi hab)

end PseudoPrime.Analysis
