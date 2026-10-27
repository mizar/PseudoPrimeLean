/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerLeadingLowerBound
public import PseudoPrime.LLS.GammaEulerGrowthChebyshev

/-! # Growing Euler credits with leading coefficients and variable block weights -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: RH, a>=100000, an initial Euler credit C and r<=(2a)^(-1/20).
Claim: doubling adds at least (2190143241/10000000000)r to the credit. Retain the positive
Euler endpoint weight and the psi block mass. Role: remove a fixed upper
cutoff from analytic prefix growth. -/
theorem gamma_euler_prefix_doubling_gain_of_leading_power_lower (hRH : RiemannHypothesis) {a : ℕ}
    (ha : 100000 ≤ a) {r C : ℝ} (hr : r ≤ ((2 : ℝ) * a) ^ (-1 / 20 : ℝ))
    (hC : C ≤ ∑ k ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight k) :
    C + (2190143241 / 10000000000 : ℝ) * r ≤
      ∑ k ∈ Finset.Ioc 0 (2 * a), Analysis.gammaResolventMangoldtWeight k := by
  have haR : (100000 : ℝ) ≤ a := by exact_mod_cast ha
  have hap := psi_bounds_of_hundred_thousand_le hRH haR
  have hbp :=
    psi_bounds_of_hundred_thousand_le hRH (show (100000 : ℝ) ≤ (2 : ℝ) * a by linarith only [haR])
  have hd : (39 / 100 : ℝ) * ((2 : ℝ) * a) ≤ Chebyshev.psi ((2 : ℝ) * a) - Chebyshev.psi a := by
    linarith only [hap.2, hbp.1]
  have he : (((2 : ℝ) * a) ^ (-21 / 20 : ℝ)) * ((2 : ℝ) * a) = ((2 : ℝ) * a) ^ (-1 / 20 : ℝ) := by
    calc
      _ = ((2 : ℝ) * a) ^ (-21 / 20 : ℝ) * ((2 : ℝ) * a) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ((2 : ℝ) * a) ^ ((-21 / 20 : ℝ) + 1) := (Real.rpow_add (by linarith only [haR]) _ _).symm
      _ = _ := by norm_num only
  have hg :=
    Analysis.gamma_euler_prefix_lower_growth_leading (by linarith only [ha] : 3 ≤ a)
      (show a ≤ 2 * a by nlinarith only [Nat.zero_le a]) hC
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, neg_div] at hg
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 56157519 / 100000000)
        (Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) * a by linarith only [haR]) (-21 / 20 : ℝ)))
  have hex :
    (56157519 / 100000000 : ℝ) * ((2 : ℝ) * a) ^ (-21 / 20 : ℝ) * ((39 / 100 : ℝ) * ((2 : ℝ) * a)) =
      (2190143241 / 10000000000 : ℝ) * ((2 : ℝ) * a) ^ (-1 / 20 : ℝ) := by
    rw [← he]
    ring
  rw [hex] at hm
  norm_num only at hg hm
  linarith only [hg, hm, hr]

/-- Input: RH, a>=100000, an initial credit C, and a lower endpoint
weight r(j) for each doubled block. Claim: k blocks add the sum of their
individual leading-coefficient gains. Proof: split at each doubled endpoint.
Role: avoid replacing every block weight by the final, smallest weight. -/
theorem gamma_euler_prefix_lower_doublings_varying (hRH : RiemannHypothesis) {a : ℕ}
    (ha : 100000 ≤ a) {C : ℝ} (r : ℕ → ℝ)
    (hC : C ≤ ∑ n ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight n)
    (hr : ∀ j, r j ≤ (a * 2 ^ (j + 1) : ℕ) ^ (-1 / 20 : ℝ)) (k : ℕ) :
    C + (2190143241 / 10000000000 : ℝ) * (∑ j ∈ Finset.range k, r j) ≤
      ∑ n ∈ Finset.Ioc 0 (a * 2 ^ k), Analysis.gammaResolventMangoldtWeight n := by
  induction k with
  | zero => simpa only [Finset.sum_range_zero, mul_zero, add_zero, pow_zero, mul_one] using hC
  | succ k ih =>
    have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num only : 0 < (2 : ℕ)) _
    have hlow : a ≤ a * 2 ^ k := by nlinarith only [hpow, Nat.zero_le a]
    have heq : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
      rw [pow_succ]; ring
    have hrc : r k ≤ ((2 : ℝ) * (a * 2 ^ k : ℕ)) ^ (-1 / 20 : ℝ) := by
      have h := hr k
      rw [heq, Nat.cast_mul, Nat.cast_ofNat] at h
      exact h
    have hg := gamma_euler_prefix_doubling_gain_of_leading_power_lower hRH (ha.trans hlow) hrc ih
    rw [heq]
    simpa only [Finset.sum_range_succ, mul_add, add_assoc] using hg

/-- Input: a positive natural a, positive r,s, and rational-power bounds
a<=(1/r)^20 and 2<=(1/s)^20. Claim: the j-th doubled endpoint has inverse
twentieth power at least r*s^(j+1). Proof: compare integer powers before
applying the antitone real power. Role: retain changing weights across blocks. -/
theorem gamma_doubling_endpoint_power_lower {a : ℕ} (ha : 0 < a) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hbase : (a : ℝ) ≤ (1 / r) ^ (20 : ℕ)) (hratio : (2 : ℝ) ≤ (1 / s) ^ (20 : ℕ)) (j : ℕ) :
    r * s ^ (j + 1) ≤ (a * 2 ^ (j + 1) : ℕ) ^ (-1 / 20 : ℝ) := by
  have hpow := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) hratio (j + 1)
  have hb : (a * 2 ^ (j + 1) : ℕ) ≤ ((1 / r) * (1 / s) ^ (j + 1)) ^ (20 : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← pow_right_comm (1 / s) 20 (j + 1)]
    exact
      mul_le_mul hbase hpow (pow_nonneg (by norm_num only) _) (pow_nonneg (one_div_pos.mpr hr).le _)
  have ha0 : (0 : ℝ) < (a * 2 ^ (j + 1) : ℕ) :=
    Nat.cast_pos.mpr (Nat.mul_pos ha (pow_pos (by norm_num only : 0 < (2 : ℕ)) _))
  have hp := Real.rpow_le_rpow_of_nonpos ha0 hb (by norm_num only : (-1 / 20 : ℝ) ≤ 0)
  have hq0 : 0 < (1 / r) * (1 / s) ^ (j + 1) :=
    mul_pos (one_div_pos.mpr hr) (pow_pos (one_div_pos.mpr hs) _)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le] at hp
  norm_num only [show (20 : ℝ) * (-1 / 20) = -1 by norm_num only, Real.rpow_neg_one, mul_inv_rev,
    one_div, inv_inv, inv_pow] at hp
  simpa only [mul_comm, neg_div] using hp

/-- Input: RH and b>=100000000. Claim: the Euler prefix is at least 839/125.
Proof: retain nine individually weighted doubling gains from the existing
100000 credit, then one partial block up to one hundred million.
Role: strengthen the analytic witness credit without enumerating prime powers. -/
theorem gamma_prefix100000000_lower_leading (hRH : RiemannHypothesis) {b : ℝ} (hb : 100000000 ≤ b) :
    (839 / 125 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n := by
  let r : ℕ → ℝ := fun j ↦ (14 / 25 : ℝ) * (28 / 29 : ℝ) ^ (j + 1)
  have hr : ∀ j, r j ≤ (100000 * 2 ^ (j + 1) : ℕ) ^ (-1 / 20 : ℝ) := by
    intro j
    exact
      gamma_doubling_endpoint_power_lower (by norm_num only : 0 < (100000 : ℕ)) (by norm_num only)
        (by norm_num only) (by norm_num only : (100000 : ℝ) ≤ (1 / (14 / 25 : ℝ)) ^ (20 : ℕ))
        (by norm_num only : (2 : ℝ) ≤ (1 / (28 / 29 : ℝ)) ^ (20 : ℕ)) j
  have hs := gamma_prefix50000_lower_asymmetric hRH (by norm_num only : (50000 : ℝ) ≤ 100000)
  have hsN :
    (28493 / 5000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 (100000 : ℕ), Analysis.gammaResolventMangoldtWeight n := by
    simpa only [Nat.floor_ofNat] using hs
  have h9 :=
    gamma_euler_prefix_lower_doublings_varying hRH (by norm_num only : (100000 : ℕ) ≤ 100000) r hsN
      hr 9
  have hg :=
    Analysis.gamma_euler_prefix_lower_growth_leading (by norm_num only : (3 : ℕ) ≤ 51200000)
      (by norm_num only : (51200000 : ℕ) ≤ 100000000) h9
  have ha := psi_bounds_of_hundred_thousand_le hRH (by norm_num only : (100000 : ℝ) ≤ 51200000)
  have hB := psi_bounds_of_hundred_thousand_le hRH (by norm_num only : (100000 : ℝ) ≤ 100000000)
  have hd :
    (4713 / 12500 : ℝ) * 100000000 ≤
      Chebyshev.psi (100000000 : ℝ) - Chebyshev.psi (51200000 : ℝ) := by
    linarith only [ha.2, hB.1]
  have hp :=
    (hr 9).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 100000000)
        (by norm_num only : (100000000 : ℝ) ≤ (100000 * 2 ^ (9 + 1) : ℕ))
        (by norm_num only : (-1 / 20 : ℝ) ≤ 0))
  have he : (100000000 : ℝ) ^ (-21 / 20 : ℝ) * 100000000 = (100000000 : ℝ) ^ (-1 / 20 : ℝ) := by
    calc
      _ = (100000000 : ℝ) ^ (-21 / 20 : ℝ) * (100000000 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (100000000 : ℝ) ^ ((-21 / 20 : ℝ) + 1) := (Real.rpow_add (by norm_num only) _ _).symm
      _ = _ := by norm_num only
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 56157519 / 100000000)
        (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 100000000) (-21 / 20 : ℝ)))
  have hmul :
    (56157519 / 100000000 : ℝ) * (100000000 : ℝ) ^ (-21 / 20 : ℝ) *
        ((4713 / 12500 : ℝ) * 100000000) =
      (56157519 / 100000000 : ℝ) * (4713 / 12500) * (100000000 : ℝ) ^ (-1 / 20 : ℝ) := by
    rw [← he]
    ring
  rw [hmul] at hm
  norm_num only [Nat.cast_ofNat, neg_div] at hg hm hp
  have hc :
    ((839 / 125 : ℚ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 (100000000 : ℕ), Analysis.gammaResolventMangoldtWeight n := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    nlinarith only [hg, hm, hp]
  have hf := Nat.floor_mono hb
  norm_num only [Nat.floor_ofNat] at hf
  have h := Analysis.gamma_euler_prefix_lower_mono hf hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Input: RH, 3<=a<=b, 1<s<b, a<t and an initial Euler credit.
Claim: the asymmetric psi block yields a gain with the exact leading coefficient.
Proof: combine the one-sided psi bounds with the stronger positive Euler weight.
Role: share the improvement with quadratic witness and MR comparisons. -/
theorem gamma_euler_prefix_lower_growth_leading_asymmetric (hRH : RiemannHypothesis) {a b : ℕ}
    {s t C : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) (hs : 1 < s) (hsb : s < b) (hat : (a : ℝ) < t)
    (hC : C ≤ ∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j) :
    C + (56157519 / 100000000 : ℝ) * (b : ℝ) ^ (-21 / 20 : ℝ) * psiAsymmetricBlockLower a b s t ≤
      ∑ j ∈ Finset.Ioc 0 b, Analysis.gammaResolventMangoldtWeight j := by
  have haR : (3 : ℝ) ≤ a := Nat.cast_le.mpr ha
  have hd :=
    psi_sub_psi_ge_asymmetric_rh_bound hRH hs hsb (by linarith only [haR] : (1 : ℝ) < a) hat
  have hm :=
    mul_le_mul_of_nonneg_left hd
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 56157519 / 100000000)
        (Real.rpow_nonneg (Nat.cast_nonneg b) (-21 / 20 : ℝ)))
  have hg := Analysis.gamma_euler_prefix_lower_growth_leading ha hab hC
  linarith only [hm, hg]

end PseudoPrime.LLS
