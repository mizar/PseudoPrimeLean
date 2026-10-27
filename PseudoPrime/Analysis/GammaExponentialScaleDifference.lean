/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerTail
public import PseudoPrime.Analysis.GammaWindowRowBounds
public import PseudoPrime.Analysis.GaussianGammaCutoffCurvature

/-! # Analytic scale differences for sparse prime-power exponential masses -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: positive atom v and scale x. Claim: v*exp(-v/x) <= 2x^2/v.
Rescale the quadratic exponential bound. Role: dominate the sparse moment tail. -/
theorem exp_moment_atom_le_reciprocal {v x : ℝ} (hv : 0 < v) (hx : 0 < x) :
    v * Real.exp (-v / x) ≤ 2 * x ^ 2 / v := by
  have h := gaussian_sq_mul_exp_neg_le_two (div_nonneg hv.le hx.le)
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg x)
  have heq : ((v / x) ^ 2 * Real.exp (-(v / x))) * x ^ 2 = v ^ 2 * Real.exp (-(v / x)) := by
    calc
      _ = ((v / x) ^ 2 * x ^ 2) * Real.exp (-(v / x)) := by ring
      _ = _ := by rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
  rw [heq, ← neg_div] at hm
  apply (le_div_iff₀ hv).mpr
  nlinarith only [hm]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: p>1 and x>0. Claim: the prime-power exponential first moment is
summable. Dominate by a reciprocal geometric series. Role: justify summation
of scale-difference bounds without differentiating an infinite series. -/
theorem summable_prime_exp_moment {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ ↦ (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hg : Summable (fun k : ℕ ↦ (2 * x ^ 2) * ((p : ℝ) ^ (k + 1))⁻¹) := by
    simpa only [Real.rpow_neg_one] using
      (summable_gamma_euler_positive_powers hpR (zero_lt_one : (0 : ℝ) < 1)).mul_left (2 * x ^ 2)
  apply hg.of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (Real.exp_pos _).le
  · intro k
    simpa only [div_eq_mul_inv] using
      exp_moment_atom_le_reciprocal (pow_pos (zero_lt_one.trans hpR) _) hx

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: p>=3, x>=1 and p^m<=x. Claim: the first m moment terms sum to
at most (3/2)x. Drop the exponential factor and sum the finite geometric
series. Role: bound the small-atom side of the moment. -/
theorem prime_exp_moment_head_le {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) (m : ℕ)
    (hlow : (p : ℝ) ^ m ≤ x) :
    (∑ k ∈ Finset.range m, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤
      (3 / 2 : ℝ) * x := by
  have hpN : 1 < p := by exact lt_of_lt_of_le (by decide : 1 < 3) hp
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith only [hpR]
  have hp0 := zero_lt_one.trans hp1
  have hx0 := zero_lt_one.trans_le hx
  have hhead :
    (∑ k ∈ Finset.range m, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤
      (3 / 2 : ℝ) * x := by
    have hsum :=
      Finset.sum_le_sum (s := Finset.range m)
        (fun k hk ↦
          mul_le_of_le_one_right (pow_nonneg (Nat.cast_nonneg p) (k + 1))
            (Real.exp_le_one_iff.mpr
              (div_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr (pow_nonneg (Nat.cast_nonneg p) (k + 1))) hx0.le)))
    have heq : (∑ k ∈ Finset.range m, (p : ℝ) ^ (k + 1)) = p * (((p : ℝ) ^ m - 1) / (p - 1)) := by
      simp only [pow_succ, ← Finset.sum_mul, geom_sum_eq hp1.ne' m]
      ring
    rw [heq, ← mul_div_assoc] at hsum
    apply hsum.trans
    apply (div_le_iff₀ (sub_pos.mpr hp1)).mpr
    have hm := mul_le_mul_of_nonneg_left hlow hp0.le
    nlinarith only [hm, mul_nonneg (by linarith only [hpR] : (0 : ℝ) ≤ p - 3) hx0.le]
  exact hhead

/-- Input: p>=3, x>=1 and x<=p^(m+1). Claim: the remaining moment tail
is at most 3x. Use the reciprocal atom envelope and its geometric sum.
Role: bound the large-atom side without a finite numerical table. -/
theorem prime_exp_moment_tail_le {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) (m : ℕ)
    (hupp : x ≤ (p : ℝ) ^ m * p) :
    (∑' k : ℕ, (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x)) ≤ 3 * x := by
  have hpN : 1 < p := by exact lt_of_lt_of_le (by decide : 1 < 3) hp
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < p := by linarith only [hpR]
  have hp0 := zero_lt_one.trans hp1
  have hx0 := zero_lt_one.trans_le hx
  have hs := summable_prime_exp_moment hpN hx0
  have hg : Summable (fun k : ℕ ↦ (2 * x ^ 2) * ((p : ℝ) ^ (k + 1))⁻¹) := by
    simpa only [Real.rpow_neg_one] using
      (summable_gamma_euler_positive_powers hp1 (zero_lt_one : (0 : ℝ) < 1)).mul_left (2 * x ^ 2)
  have ht :=
    ((summable_nat_add_iff m).mpr hs).tsum_le_tsum
      (fun k ↦
        show
          (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x) ≤
            (2 * x ^ 2) * ((p : ℝ) ^ (k + m + 1))⁻¹
          from by
          simpa only [div_eq_mul_inv] using exp_moment_atom_le_reciprocal (pow_pos hp0 _) hx0)
      ((summable_nat_add_iff m).mpr hg)
  rw [gamma_reciprocal_power_tail_sum hp1 m] at ht
  have htail :
    (∑' k : ℕ, (p : ℝ) ^ (k + m + 1) * Real.exp (-((p : ℝ) ^ (k + m + 1)) / x)) ≤ 3 * x := by
    apply ht.trans
    apply (div_le_iff₀ (mul_pos (pow_pos hp0 _) (sub_pos.mpr hp1))).mpr
    have hprod : 2 * x ≤ 3 * (p : ℝ) ^ m * (p - 1) := by
      nlinarith only [hupp,
        mul_nonneg (pow_pos hp0 m).le (by linarith only [hpR] : (0 : ℝ) ≤ p - 3)]
    nlinarith only [mul_le_mul_of_nonneg_right hprod hx0.le]
  exact htail

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: p>=3 and x>=1. Claim: the complete prime-power exponential
moment is at most (9/2)x. Split at floor(log(x)/log(p)) and combine both
geometric bounds. Role: supply a base-independent scale modulus. -/
theorem prime_exp_moment_le_nine_halves {p : ℕ} (hp : 3 ≤ p) {x : ℝ} (hx : 1 ≤ x) :
    (∑' k : ℕ, (p : ℝ) ^ (k + 1) * Real.exp (-((p : ℝ) ^ (k + 1)) / x)) ≤ (9 / 2 : ℝ) * x := by
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
  have htail := prime_exp_moment_tail_le hp hx m hupp
  have heq := hs.sum_add_tsum_nat_add m
  linarith only [heq, hhead, htail]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: real v,a,b. Claim: the exponential scale difference is bounded
by the reciprocal-scale difference times its first moment atom. Apply the
exponential tangent inequality. Role: avoid differentiating the series. -/
theorem exp_neg_scale_difference_le (v a b : ℝ) :
    Real.exp (-v / b) - Real.exp (-v / a) ≤ (1 / a - 1 / b) * (v * Real.exp (-v / b)) := by
  have ht := Real.add_one_le_exp (-(v * (1 / a - 1 / b)))
  have hm := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-v / b)).le
  rw [← Real.exp_add, show -v / b + -(v * (1 / a - 1 / b)) = -v / a by ring] at hm
  nlinarith only [hm]

/-- Input: p>=3, 0<a<=b and b>=1. Claim: the complete exponential mass
gain is at most (9/2)(b-a)/a. Sum the atom tangent bound and apply the
uniform moment estimate. Role: move a certified left endpoint downward. -/
theorem gamma_prime_exponential_mass_difference_le {p : ℕ} (hp : 3 ≤ p) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaPrimeExponentialMass p b - gammaPrimeExponentialMass p a ≤ (9 / 2 : ℝ) * (b - a) / a := by
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
  have hm := mul_le_mul_of_nonneg_left (prime_exp_moment_le_nine_halves hp hb) hd
  have heq : (1 / a - 1 / b) * ((9 / 2 : ℝ) * b) = (9 / 2 : ℝ) * (b - a) / a := by
    calc
      _ = (9 / 2 : ℝ) * (b / a - b / b) := by ring
      _ = (9 / 2 : ℝ) * (b / a - 1) := by rw [div_self hb0.ne']
      _ = _ := by rw [div_sub_one ha.ne', mul_div_assoc]
  rw [heq] at hm
  simpa only [gammaPrimeExponentialMass, neg_div] using ht.trans hm

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: p>=3 and positive ordered left endpoints a<=b with b>=1.
Claim: moving the left endpoint to a increases the signed window numerator
by at most (9/2)(b-a)/a. Use the exponential mass difference.
Role: reuse an existing interval certificate on a larger interval. -/
theorem gamma_ramified_window_numerator_le_lowered_left {p : ℕ} (hp : 3 ≤ p) {a b hi θ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaRamifiedWindowNumerator p a hi θ ≤
      gammaRamifiedWindowNumerator p b hi θ + (9 / 2 : ℝ) * (b - a) / a := by
  have h := gamma_prime_exponential_mass_difference_le hp ha hab hb
  dsimp only [gammaRamifiedWindowNumerator]
  linarith only [h]

/-- Input: an envelope-checked prime row with p>=3 and a new positive left
endpoint below the old one. Claim: its stored ramp cap plus the common
scale correction bounds the new numerator. Role: reuse numerical row data. -/
theorem GammaLocalPrimeRow.window_numerator_le_lowered_left (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime) (h3 : 3 ≤ r.prime)
    (hc : r.envelopeCheck c = true) {a : ℝ} (ha : 0 < a) (hab : a ≤ (c.lo : ℝ))
    (hb : (1 : ℝ) ≤ c.lo) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime a c.hi θ ≤
      (r.rampUpper : ℝ) - θ + (9 / 2 : ℝ) * ((c.lo : ℝ) - a) / a := by
  have hs := gamma_ramified_window_numerator_le_lowered_left h3 ha hab hb (hi := c.hi) (θ := θ)
  have hr := r.window_numerator_le_of_envelope c hcell hp hc θ
  linarith only [hs, hr]

end PseudoPrime.Analysis
