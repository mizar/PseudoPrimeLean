/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaExponentialScaleDifference

/-! # Analytic improvement of the prime-power scale modulus from 9/2 to 3 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: z>=0. Claim: z²exp(-z)<=1. Square 2t<=exp(t) at t=z/2.
Role: sharpen the reciprocal envelope without numerical certification. -/
theorem sq_mul_exp_neg_le_one {z : ℝ} (hz : 0 ≤ z) : z ^ 2 * Real.exp (-z) ≤ 1 := by
  have h : z ≤ Real.exp (z / 2) := by nlinarith only [Real.two_mul_le_exp (x := z / 2)]
  have hs := mul_self_le_mul_self hz h
  rw [← Real.exp_add, show z / 2 + z / 2 = z by ring] at hs
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-z)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  nlinarith only [hm]

/-- Input: positive atom v and scale x. Claim: v exp(-v/x)<=x²/v.
Rescale the quadratic exponential bound. Role: halve the old tail envelope. -/
theorem exp_moment_atom_le_half_reciprocal {v x : ℝ} (hv : 0 < v) (hx : 0 < x) :
    v * Real.exp (-v / x) ≤ x ^ 2 / v := by
  have h := sq_mul_exp_neg_le_one (div_nonneg hv.le hx.le)
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
  have heq : ((v / x) ^ 2 * Real.exp (-(v / x))) * x ^ 2 = v ^ 2 * Real.exp (-(v / x)) := by
    calc
      _ = ((v / x) ^ 2 * x ^ 2) * Real.exp (-(v / x)) := by ring
      _ = _ := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
  rw [heq, ← neg_div] at hm
  apply (le_div_iff₀ hv).mpr
  nlinarith only [hm]

/-- Input: p>=3, x>=1, and x<=p^(m+1). Claim: the remaining exponential
moment tail is at most (3/2)x. Sum the sharper reciprocal geometric envelope.
Role: improve scale transport without additional prime-power tables. -/
theorem prime_exp_moment_tail_le_three_halves {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) (m : ℕ)
    (hupp : x ≤ (p : ℝ) ^ m * p) :
    (∑' k : ℕ, (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x)) ≤
      (3 / 2 : ℝ) * x := by
  have hpN : 1 < p := by exact lt_of_lt_of_le (by decide : 1 < 3) hp
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith only [hpR]
  have hp0 := zero_lt_one.trans hp1
  have hx0 := zero_lt_one.trans_le hx
  have hs := summable_prime_exp_moment hpN hx0
  have hg : Summable (fun k : ℕ ↦ (x ^ 2) * ((p : ℝ) ^ (k + 1))⁻¹) := by
    simpa only [Real.rpow_neg_one] using
      (summable_gamma_euler_positive_powers hp1 (zero_lt_one : (0 : ℝ) < 1)).mul_left (x ^ 2)
  have ht :=
    ((summable_nat_add_iff m).mpr hs).tsum_le_tsum
      (fun k ↦
        show
          (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x) ≤
            (x ^ 2) * ((p : ℝ) ^ (k + m + 1))⁻¹
          from by
          simpa only [div_eq_mul_inv] using exp_moment_atom_le_half_reciprocal (pow_pos hp0 _) hx0)
      ((summable_nat_add_iff m).mpr hg)
  rw [gamma_reciprocal_power_tail_sum hp1 m] at ht
  have htail :
    (∑' k : ℕ, (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x)) ≤
      (3 / 2 : ℝ) * x := by
    apply ht.trans
    apply (div_le_iff₀ (mul_pos (pow_pos hp0 _) (sub_pos.mpr hp1))).mpr
    have hprod : x ≤ (3 / 2 : ℝ) * (p : ℝ) ^ m * (p - 1) := by
      nlinarith only [hupp,
        mul_nonneg (pow_pos hp0 m).le (by linarith only [hpR] : (0 : ℝ) ≤ p - 3)]
    nlinarith only [mul_le_mul_of_nonneg_right hprod hx0.le]
  exact htail

/-- Input: p>=3 and x>=1. Claim: the full exponential moment is at most 3x.
Split at the logarithmic floor and combine the existing head with the sharper tail.
Role: supply a stronger uniform modulus for the entire scale interval. -/
theorem prime_exp_moment_le_three {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    (∑' k : ℕ, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤ 3 * x := by
  have hpN : 1 < p := by exact lt_of_lt_of_le (by decide : 1 < 3) hp
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith only [hpR]
  have hp0 := zero_lt_one.trans hp1
  have hx0 := zero_lt_one.trans_le hx
  let m := ⌊Real.log x / Real.log p⌋₊
  have hlow : (p : ℝ) ^ m ≤ x := by
    apply (Real.log_le_log_iff (pow_pos hp0 _) hx0).mp
    rw [Real.log_pow]
    have hf := Nat.floor_le (div_nonneg (Real.log_nonneg hx) (Real.log_pos hp1).le)
    exact (le_div_iff₀ (Real.log_pos hp1)).mp hf
  have hupp : x ≤ (p : ℝ) ^ m * p := by
    have ht := prime_power_above_log_floor hpN hx0
    rw [pow_succ] at ht
    exact ht.le
  have hs := summable_prime_exp_moment hpN hx0
  have hhead := prime_exp_moment_head_le hp hx m hlow
  have htail := prime_exp_moment_tail_le_three_halves hp hx m hupp
  have heq := hs.sum_add_tsum_nat_add m
  linarith only [heq, hhead, htail]

/-- Input: p>=3, 0<a<=b and b>=1. Claim: the exponential mass gain is
at most 3(b-a)/a. Sum tangent bounds using the improved moment.
Role: decrease the common correction in downward window transport. -/
theorem gamma_prime_exponential_mass_difference_le_three {p : ℕ} (hp : 3 ≤ p) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaPrimeExponentialMass p b - gammaPrimeExponentialMass p a ≤ (3 : ℝ) * (b - a) / a := by
  have hpN : 1 < p := lt_of_lt_of_le (by decide : 1 < 3) hp
  have hb0 := zero_lt_one.trans_le hb
  have hsa := summable_exp_neg_of_linear_lower ha _ (prime_power_div_scale_ge_linear hpN ha)
  have hsb := summable_exp_neg_of_linear_lower hb0 _ (prime_power_div_scale_ge_linear hpN hb0)
  have hd : 0 ≤ 1 / a - 1 / b :=
    sub_nonneg.mpr (div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 1) le_rfl ha hab)
  simp only [← neg_div] at hsa hsb
  have ht :=
    (hsb.sub hsa).tsum_le_tsum (fun k ↦ exp_neg_scale_difference_le ((p : ℝ) ^ (k + 1)) a b)
      ((summable_prime_exp_moment hpN hb0).mul_left (1 / a - 1 / b))
  rw [hsb.tsum_sub hsa, tsum_mul_left] at ht
  have hm := mul_le_mul_of_nonneg_left (prime_exp_moment_le_three hp hb) hd
  have heq : (1 / a - 1 / b) * ((3 : ℝ) * b) = (3 : ℝ) * (b - a) / a := by
    calc
      _ = (3 : ℝ) * (b / a - b / b) := by ring
      _ = (3 : ℝ) * (b / a - 1) := by rw [div_self hb0.ne']
      _ = _ := by rw [div_sub_one ha.ne', mul_div_assoc]
  rw [heq] at hm
  simpa only [gammaPrimeExponentialMass, neg_div] using ht.trans hm

/-- Input: p>=3 and positive ordered endpoints a<=b with b>=1.
Claim: lowering the left endpoint increases the numerator by at most 3(b-a)/a.
Use the mass difference. Role: transport existing signed numerator bounds. -/
theorem gamma_ramified_window_numerator_le_lowered_left_three {p : ℕ} (hp : 3 ≤ p) {a b hi θ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaRamifiedWindowNumerator p a hi θ ≤
      gammaRamifiedWindowNumerator p b hi θ + (3 : ℝ) * (b - a) / a := by
  have h := gamma_prime_exponential_mass_difference_le_three hp ha hab hb
  dsimp only [gammaRamifiedWindowNumerator]
  linarith only [h]

/-- Input: an envelope-checked prime row with p>=3 and a new positive left
endpoint below the old one. Claim: its stored ramp cap plus the common
scale correction bounds the new numerator. Role: reuse numerical row data. -/
theorem GammaLocalPrimeRow.window_numerator_le_lowered_left_three (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime) (h3 : 3 ≤ r.prime)
    (hc : r.envelopeCheck c = true) {a : ℝ} (ha : 0 < a) (hab : a ≤ (c.lo : ℝ))
    (hb : (1 : ℝ) ≤ c.lo) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime a c.hi θ ≤
      (r.rampUpper : ℝ) - θ + (3 : ℝ) * ((c.lo : ℝ) - a) / a := by
  have hs :=
    gamma_ramified_window_numerator_le_lowered_left_three h3 ha hab hb (hi := c.hi) (θ := θ)
  have hr := r.window_numerator_le_of_envelope c hcell hp hc θ
  linarith only [hs, hr]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: p>1, 0<a<=x<=pa. Claim: the head and tail geometric caps sum
to at most ((p+1)/(p-1))x. Use (x-a)(pa-x)>=0 without maximizing each cap
separately. Role: retain the coupling at the logarithmic split. -/
theorem coupled_geometric_moment_bound {p a x : ℝ} (hp : 1 < p) (ha0 : 0 < a) (ha : a ≤ x)
    (hx : x ≤ p * a) : p * a / (p - 1) + x ^ 2 / (a * (p - 1)) ≤ (p + 1) / (p - 1) * x := by
  have hdiv : x ^ 2 / a ≤ (p + 1) * x - p * a := by
    apply (div_le_iff₀ ha0).mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hx)]
  calc
    _ = (p * a + x ^ 2 / a) / (p - 1) := by rw [add_div, div_div]
    _ ≤ ((p + 1) * x) / (p - 1) :=
      div_le_div_of_nonneg_right (by linarith only [hdiv]) (sub_pos.mpr hp).le
    _ = _ := by ring

/-- Input: p>1, x>0 and a split index m. Claim: the first m exponential
moment terms are bounded by p*p^m/(p-1). Drop only the exponential factors.
Role: retain the split scale for the coupled comparison. -/
theorem prime_exp_moment_head_le_geometric {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (∑ k ∈ Finset.range m, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤
      p * (p : ℝ) ^ m / (p - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hs :=
    Finset.sum_le_sum (s := Finset.range m)
      (fun k hk ↦
        mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg p) (k + 1))
          (Real.exp_le_one_iff.mpr
            (div_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr (pow_nonneg (Nat.cast_nonneg p) (k + 1))) hx.le)))
  have heq : (∑ k ∈ Finset.range m, (p : ℝ) ^ (k + 1)) = p * (((p : ℝ) ^ m - 1) / (p - 1)) := by
    simp only [pow_succ, ← Finset.sum_mul, geom_sum_eq hp1.ne' m]
    ring
  rw [heq, ← mul_div_assoc] at hs
  exact
    hs.trans
      (div_le_div_of_nonneg_right (by nlinarith only [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
        (sub_pos.mpr hp1).le)

/-- Input: p>1, x>0 and a split index m. Claim: the remaining moment is
at most x²/(p^m(p-1)). Sum the reciprocal envelope without replacing p^m
by x/p. Role: retain the coupling with the head. -/
theorem prime_exp_moment_tail_le_geometric {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (∑' k : ℕ, (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x)) ≤
      x ^ 2 / ((p : ℝ) ^ m * (p - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 := zero_lt_one.trans hp1
  have hs := summable_prime_exp_moment hp hx
  have hg : Summable (fun k : ℕ ↦ x ^ 2 * ((p : ℝ) ^ (k + 1))⁻¹) := by
    simpa only [Real.rpow_neg_one] using
      (summable_gamma_euler_positive_powers hp1 (zero_lt_one : (0 : ℝ) < 1)).mul_left (x ^ 2)
  have ht :=
    ((summable_nat_add_iff m).mpr hs).tsum_le_tsum
      (fun k ↦
        show
          (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x) ≤
            x ^ 2 * ((p : ℝ) ^ (k + m + 1))⁻¹
          from by
          simpa only [div_eq_mul_inv] using exp_moment_atom_le_half_reciprocal (pow_pos hp0 _) hx)
      ((summable_nat_add_iff m).mpr hg)
  rw [gamma_reciprocal_power_tail_sum hp1 m] at ht
  exact ht

/-- Input: p>1 and x>=1. Claim: the complete exponential moment is at most
((p+1)/(p-1))x. Split at the logarithmic floor and combine the geometric caps
before relaxing the split scale. Role: provide a base-sensitive transport modulus. -/
theorem prime_exp_moment_le_base_ratio {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    (∑' k : ℕ, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤
      ((p : ℝ) + 1) / (p - 1) * x := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 := zero_lt_one.trans hp1
  have hx0 := zero_lt_one.trans_le hx
  let m := ⌊Real.log x / Real.log p⌋₊
  have hlow : (p : ℝ) ^ m ≤ x := by
    apply (Real.log_le_log_iff (pow_pos hp0 _) hx0).mp
    rw [Real.log_pow]
    have hf := Nat.floor_le (div_nonneg (Real.log_nonneg hx) (Real.log_pos hp1).le)
    exact (le_div_iff₀ (Real.log_pos hp1)).mp hf
  have hupp : x ≤ (p : ℝ) ^ m * p := by
    have ht := prime_power_above_log_floor hp hx0
    rw [pow_succ] at ht
    exact ht.le
  have hs := summable_prime_exp_moment hp hx0
  have hhead := prime_exp_moment_head_le_geometric hp hx0 m
  have htail := prime_exp_moment_tail_le_geometric hp hx0 m
  have heq := hs.sum_add_tsum_nat_add m
  calc
    _ = _ := heq.symm
    _ ≤ _ := add_le_add hhead htail
    _ ≤ _ :=
      coupled_geometric_moment_bound hp1 (pow_pos hp0 m) hlow (by simpa only [mul_comm] using hupp)

/-- Input: p>=3 and x>=1. Claim: the complete exponential moment is at most
2x. Bound the base-sensitive ratio by two. Role: improve the uniform modulus. -/
theorem prime_exp_moment_le_two {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    (∑' k : ℕ, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤ 2 * x := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hp)
  have hr : ((p : ℝ) + 1) / (p - 1) ≤ 2 := by
    apply (div_le_iff₀ (sub_pos.mpr hp1)).mpr
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith only [hp3]
  exact
    (prime_exp_moment_le_base_ratio (lt_of_lt_of_le (by decide : 1 < 3) hp) hx).trans
      (mul_le_mul_of_nonneg_right hr (zero_lt_one.trans_le hx).le)

/-- Input: p>1, 0<a<=b and b>=1. Claim: the exponential mass gain is at most
((p+1)/(p-1))(b-a)/a. Sum tangent bounds using the coupled moment estimate.
Role: preserve the improved coefficient in each row of a transported window. -/
theorem gamma_prime_exponential_mass_difference_le_base_ratio {p : ℕ} (hp : 1 < p) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaPrimeExponentialMass p b - gammaPrimeExponentialMass p a ≤
      (((p : ℝ) + 1) / (p - 1)) * (b - a) / a := by
  have hb0 := zero_lt_one.trans_le hb
  have hsa := summable_exp_neg_of_linear_lower ha _ (prime_power_div_scale_ge_linear hp ha)
  have hsb := summable_exp_neg_of_linear_lower hb0 _ (prime_power_div_scale_ge_linear hp hb0)
  have hd : 0 ≤ 1 / a - 1 / b :=
    sub_nonneg.mpr (div_le_div₀ (by norm_num only : (0 : ℝ) ≤ 1) le_rfl ha hab)
  simp only [← neg_div] at hsa hsb
  have ht :=
    (hsb.sub hsa).tsum_le_tsum (fun k ↦ exp_neg_scale_difference_le ((p : ℝ) ^ (k + 1)) a b)
      ((summable_prime_exp_moment hp hb0).mul_left (1 / a - 1 / b))
  rw [hsb.tsum_sub hsa, tsum_mul_left] at ht
  have hm := mul_le_mul_of_nonneg_left (prime_exp_moment_le_base_ratio hp hb) hd
  have heq :
    (1 / a - 1 / b) * ((((p : ℝ) + 1) / (p - 1)) * b) =
      (((p : ℝ) + 1) / (p - 1)) * (b - a) / a := by
    calc
      _ = (((p : ℝ) + 1) / (p - 1)) * (b / a - b / b) := by ring
      _ = (((p : ℝ) + 1) / (p - 1)) * (b / a - 1) := by rw [div_self hb0.ne']
      _ = _ := by rw [div_sub_one ha.ne', mul_div_assoc]
  rw [heq] at hm
  simpa only [gammaPrimeExponentialMass, neg_div] using ht.trans hm

/-- Input: a checked cell, an envelope-checked prime row and a lower positive
left endpoint. Claim: the old ramp cap with its base-sensitive correction bounds
the new numerator. Use the analytic mass difference and existing row bound.
Role: lower a window without generating new prime-specific data. -/
theorem GammaLocalPrimeRow.window_numerator_le_lowered_left_base_ratio (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime)
    (hc : r.envelopeCheck c = true) {a : ℝ} (ha : 0 < a) (hab : a ≤ (c.lo : ℝ))
    (hb : (1 : ℝ) ≤ c.lo) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime a c.hi θ ≤
      (r.rampUpper : ℝ) - θ + (((r.prime : ℝ) + 1) / (r.prime - 1)) * ((c.lo : ℝ) - a) / a := by
  have hs := gamma_prime_exponential_mass_difference_le_base_ratio hp.one_lt ha hab hb
  have hr := r.window_numerator_le_of_envelope c hcell hp hc θ
  dsimp only [gammaRamifiedWindowNumerator] at hs hr ⊢
  linarith only [hs, hr]

end PseudoPrime.Analysis
