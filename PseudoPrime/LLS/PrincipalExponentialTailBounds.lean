/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrincipalRampEndpointBounds
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Finite-prefix and geometric-tail principal-ramp bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For 0<=r<1, the shifted linear geometric series has the displayed sum.
Combine the ordinary and linearly weighted geometric series and factor r^N.
This evaluates the elementary majorant of an exponential Mangoldt tail. -/
theorem hasSum_shifted_linear_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    HasSum (fun k : ℕ ↦ ((k + N : ℕ) : ℝ) * r ^ (k + N))
      (r ^ N * (r / (1 - r) ^ 2 + (N : ℝ) / (1 - r))) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h :=
    ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
          ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (N : ℝ))).mul_left
      (r ^ N)
  convert h using 1
  · ext k
    rw [Nat.cast_add, pow_add]
    ring
  · rw [div_eq_mul_inv (N : ℝ)]

/-- For every natural index, the Mangoldt value is at most the real index.
Handle zero separately and combine the logarithm upper bound with log(n)<=n-1. -/
theorem vonMangoldt_le_self (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, Nat.cast_zero]
  · have h := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    linarith only [ArithmeticFunction.vonMangoldt_le_log (n := n), h]

/-- At positive scale and any natural cutoff N, the principal exponential mass
is at most its range-N prefix plus the explicit shifted linear geometric tail.
Use Lambda(n)<=n, exact exponential powers and convergent series splitting. RH is unnecessary. -/
theorem principalExponentialMass_le_finite_add_tail {x : ℝ} (hx : 0 < x) (N : ℕ) :
    principalExponentialMass x ≤
      (∑ n ∈ Finset.range N, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n) +
        Real.exp (-1 / x) ^ N *
          (Real.exp (-1 / x) / (1 - Real.exp (-1 / x)) ^ 2 +
            (N : ℝ) / (1 - Real.exp (-1 / x))) := by
  let r := Real.exp (-1 / x)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num only) hx)
  have hmajor := hasSum_shifted_linear_geometric hr0 hr1 N
  have hsmall := (summable_nat_add_iff N).mpr (summable_principalExponentialMass hx)
  have ht := Summable.tsum_le_tsum (fun k ↦ ?_) hsmall hmajor.summable
  · have he := (summable_principalExponentialMass hx).sum_add_tsum_nat_add N
    dsimp only [principalExponentialMass]
    rw [← he]
    exact add_le_add le_rfl (ht.trans_eq hmajor.tsum_eq)
  · have he : Real.exp (-((k + N : ℕ) : ℝ) / x) = r ^ (k + N) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact
      (mul_le_mul_of_nonneg_left (vonMangoldt_le_self (k + N)) (pow_nonneg hr0 _)).trans_eq
        (mul_comm _ _)

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- The explicit upper bound for the exponential Mangoldt tail from index N.
It is r^N*(r/(1-r)^2+N/(1-r)), where r=exp(-1/x); at positive scale 0<r<1.
This replaces a full-series numerical premise with finite-prefix and scalar bounds. -/
noncomputable def principalExponentialTailBound (x : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-1 / x) ^ N *
    (Real.exp (-1 / x) / (1 - Real.exp (-1 / x)) ^ 2 + (N : ℝ) / (1 - Real.exp (-1 / x)))

/-- On a positive real interval, finite lower ramp and upper exponential
prefix estimates, plus a scalar geometric-tail bound, give C/R below the actual
principal-ramp difference. Combine the proved tail estimate with endpoint monotonicity.
No integer-modulus enumeration or RH premise is needed. -/
theorem principalRampDifference_lower_of_finite_endpoints {a b x C R r p e : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) (N : ℕ)
    (hr : r ≤ AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum a)
    (hp : (∑ n ∈ Finset.range N, Real.exp (-(n : ℝ) / b) * ArithmeticFunction.vonMangoldt n) ≤ p)
    (he : principalExponentialTailBound b N ≤ e) (hC : C ≤ 2 * r - p - e) (hC0 : 0 ≤ C)
    (hR : Real.sqrt b ≤ R) : C / R ≤ principalRampDifference x := by
  have hb := (ha.trans_le hax).trans_le hxb
  have hP := principalExponentialMass_le_finite_add_tail hb N
  apply principalRampDifference_lower_of_endpoints ha hax hxb _ hC0 hR
  change principalExponentialTailBound b N ≤ e at he
  dsimp only [principalExponentialTailBound] at he
  linarith only [hC, hr, hp, he, hP]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- At positive scale, the geometric exponential tail is at most
exp(-N/x)*(x+1)*(x+N). Use exp(1/x)>=1+1/x to bound both reciprocal factors.
This form needs only one exponential interval and polynomial arithmetic. -/
theorem principalExponentialTailBound_le_polynomial {x : ℝ} (hx : 0 < x) (N : ℕ) :
    principalExponentialTailBound x N ≤ Real.exp (-(N : ℝ) / x) * (x + 1) * (x + N) := by
  let r := Real.exp (-1 / x)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num only) hx)
  have hd : 0 < 1 - r := sub_pos.mpr hr1
  have hex := Real.add_one_le_exp (1 / x)
  have hmul := mul_le_mul_of_nonneg_right hex (mul_nonneg hr0.le hx.le)
  have hid : Real.exp (1 / x) * (r * x) = x := by
    dsimp only [r]
    rw [neg_div, Real.exp_neg]
    rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul]
  rw [hid] at hmul
  have hrel : r * (x + 1) ≤ x := by
    have hc : (1 / x) * (r * x) = r := by rw [mul_left_comm, one_div_mul_cancel hx.ne', mul_one]
    rw [add_mul, hc, one_mul] at hmul
    nlinarith only [hmul]
  have h1 : 1 / (1 - r) ≤ x + 1 := (div_le_iff₀ hd).mpr (by nlinarith only [hrel])
  have h2 : r / (1 - r) ≤ x := (div_le_iff₀ hd).mpr (by nlinarith only [hrel])
  have h3 := mul_le_mul h2 h1 (div_nonneg zero_le_one hd.le) hx.le
  have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hpoly : r / (1 - r) ^ 2 + (N : ℝ) / (1 - r) ≤ (x + 1) * (x + N) := by
    rw [show r / (1 - r) ^ 2 = (r / (1 - r)) * (1 / (1 - r)) by
        rw [div_mul_div_comm, mul_one, ← pow_two],
      show (N : ℝ) / (1 - r) = (N : ℝ) * (1 / (1 - r)) by ring]
    nlinarith only [h3, h4]
  have heq : r ^ N = Real.exp (-(N : ℝ) / x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  dsimp only [principalExponentialTailBound]
  change r ^ N * _ ≤ _
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le).trans_eq (by ring)

/-- The exponential at -24 is at most 10^-10. Raise the certified lower
bound exp(1)>=27/10 to power 24 and invert. This supplies a compact tail allowance. -/
theorem exp_neg_twenty_four_le : Real.exp (-24 : ℝ) ≤ 1 / 10000000000 := by
  have h1 : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 27 / 10) h1 24
  have ht : (10000000000 : ℝ) ≤ (27 / 10 : ℝ) ^ 24 := by norm_num only
  have he : Real.exp (24 : ℝ) = Real.exp 1 ^ 24 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 24
  rw [← he] at hp
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num only : (0 : ℝ) < 10000000000) (ht.trans hp)

/-- On every positive scale through 1660, the exponential Mangoldt tail
from index 40000 has allowance at most 1/100. Combine the polynomial-tail bound,
the scalar exponential bound at -24 and positive polynomial monotonicity. -/
theorem principalExponentialTailBound_40000_le {x : ℝ} (hx : 0 < x) (hxb : x ≤ 1660) :
    principalExponentialTailBound x 40000 ≤ 1 / 100 := by
  have ht := principalExponentialTailBound_le_polynomial hx 40000
  have he : Real.exp (-(40000 : ℝ) / x) ≤ 1 / 10000000000 :=
    (Real.exp_le_exp.mpr ((div_le_iff₀ hx).mpr (by linarith only [hxb]))).trans
      exp_neg_twenty_four_le
  have hm :=
    mul_le_mul_of_nonneg_right he
      (mul_nonneg (by linarith only [hx] : 0 ≤ x + 1) (by linarith only [hx] : 0 ≤ x + 40000))
  have hp : (x + 1) * (x + 40000) ≤ (1661 : ℝ) * 41660 := by
    exact
      mul_le_mul (by linarith only [hxb]) (by linarith only [hxb]) (by linarith only [hx])
        (by norm_num only)
  nlinarith only [ht, hm, hp]

end PseudoPrime.LLS
