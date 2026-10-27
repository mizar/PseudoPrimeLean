/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerPositiveLowerBound

/-! # Retaining the exact leading coefficient in positive Euler blocks -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: an antitone weight, nonnegative at seven, and a twofold drop
between nodes 34/20 and 46/20. Claim: the full signed combination retains
its exact leading coefficient. Proof: compare the remaining ordered nodes.
Role: strengthen positive Euler block growth without new prime data. -/
theorem gammaResolvent_weighted_ge_leading (w : ℚ → ℝ) (hw : Antitone w) (hzero : 0 ≤ w 7)
    (hgap : 2 * w (46 / 20) ≤ w (34 / 20)) :
    (56157519 / 100000000 : ℝ) * w (11 / 20) ≤
      (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * w ab.1)).sum := by
  have h1 := hw (by norm_num only : (11 / 20 : ℚ) ≤ 16 / 20)
  have h2 := hw (by norm_num only : (16 / 20 : ℚ) ≤ 20 / 20)
  have h3 := hw (by norm_num only : (20 / 20 : ℚ) ≤ 34 / 20)
  have h4 := hw (by norm_num only : (34 / 20 : ℚ) ≤ 46 / 20)
  have h5 := hw (by norm_num only : (46 / 20 : ℚ) ≤ 64 / 20)
  have h6 := hw (by norm_num only : (64 / 20 : ℚ) ≤ 90 / 20)
  have h7 := hw (by norm_num only : (90 / 20 : ℚ) ≤ 140 / 20)
  norm_num only [gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at ⊢ h1 h2 h3 h4 h5 h6 h7 hgap hzero
  linarith only [h1, h2, h3, h4, h5, h6, h7, hgap, hzero]

/-- Input: t>=4. Claim: the signed Euler weight retains its leading
coefficient times t^(-21/20). Proof: a square-root comparison supplies the
required drop between nodes. Role: improve all subsequent positive block gains. -/
theorem gamma_resolvent_euler_weight_ge_leading_power {t : ℝ} (ht : 4 ≤ t) :
    (56157519 / 100000000 : ℝ) * t ^ (-21 / 20 : ℝ) ≤ gammaResolventEulerWeight t := by
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hanti : Antitone (fun a : ℚ ↦ t ^ (-(1 / 2 + (a : ℝ)))) := by
    intro a b hab
    exact
      Real.rpow_le_rpow_of_exponent_le ht1 (neg_le_neg (add_le_add le_rfl (Rat.cast_le.mpr hab)))
  have hs : (2 : ℝ) ≤ Real.sqrt t :=
    (Real.le_sqrt (by norm_num only) ht0.le).mpr (by linarith only [ht])
  rw [Real.sqrt_eq_rpow] at hs
  have hp := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num only : (1 / 2 : ℝ) ≤ 3 / 5)
  have hgap := mul_le_mul_of_nonneg_right (hs.trans hp) (Real.rpow_nonneg ht0.le (-14 / 5 : ℝ))
  rw [← Real.rpow_add ht0] at hgap
  norm_num only at hgap
  have h :=
    gammaResolvent_weighted_ge_leading _ hanti (Real.rpow_nonneg ht0.le _)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]
        exact hgap)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [gammaResolventEulerWeight, neg_div] using h

/-- Input: natural endpoints 3<=a<=b. Claim: the Euler interval sum is
at least the leading coefficient times b^(-21/20) times psi(b)-psi(a). Compare every positive index
with the endpoint power. Role: retain a positive prime-power block analytically. -/
theorem gamma_euler_interval_lower_of_leading_psi {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    (56157519 / 100000000 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * (Chebyshev.psi b - Chebyshev.psi a) ≤
      ∑ n ∈ Finset.Ioc a b, gammaResolventMangoldtWeight n := by
  have hp :
    Chebyshev.psi b - Chebyshev.psi a = ∑ n ∈ Finset.Ioc a b, ArithmeticFunction.vonMangoldt n := by
    simp only [Chebyshev.psi, Nat.floor_natCast]
    linarith only [gamma_prefix_split hab (fun n ↦ ArithmeticFunction.vonMangoldt n)]
  rw [hp, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le a) (Finset.mem_Ioc.mp hn).1
  have hn4 : 4 ≤ n := Nat.succ_le_of_lt (ha.trans_lt (Finset.mem_Ioc.mp hn).1)
  have hnb : (n : ℝ) ≤ b := Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2
  have hpow :=
    Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hn0) hnb (by norm_num only : (-21 / 20 : ℝ) ≤ 0)
  have hl :=
    (mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 56157519 / 100000000)).trans
      (gamma_resolvent_euler_weight_ge_leading_power (t := (n : ℝ)) (by exact_mod_cast hn4))
  simpa only [gammaResolventMangoldtWeight, mul_comm] using
    (mul_le_mul_of_nonneg_right hl (ArithmeticFunction.vonMangoldt_nonneg (n := n)))

/-- Input: a proved prefix lower bound and 3<=a<=b. Claim: it grows
by the leading coefficient times b^(-21/20)(psi(b)-psi(a)). Split the prefix and add the interval
bound. Role: strengthen fixed prefix credits without new finite certificates. -/
theorem gamma_euler_prefix_lower_growth_leading {a b : ℕ} {C : ℝ} (ha : 3 ≤ a) (hab : a ≤ b)
    (hC : C ≤ ∑ n ∈ Finset.Ioc 0 a, gammaResolventMangoldtWeight n) :
    C +
        (56157519 / 100000000 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) *
          (Chebyshev.psi b - Chebyshev.psi a) ≤
      ∑ n ∈ Finset.Ioc 0 b, gammaResolventMangoldtWeight n := by
  rw [gamma_prefix_split hab]
  exact add_le_add hC (gamma_euler_interval_lower_of_leading_psi ha hab)

end PseudoPrime.Analysis
