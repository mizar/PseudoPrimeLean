/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireZeroMass

/-!
# Power-weighted zero mass from entire growth

Jensen and dyadic shells give any weight exponent strictly above the growth exponent.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For any complex function F, real exponent p and complex z, divide the natural analytic
multiplicity at z by (1+norm z)^p. The positive denominator removes a singularity at zero.
For an entire F nonzero at zero with exponential growth exponent r >= 0, these weights
are summable when p > r and p > 0; they supply majorants for zero-resolvent integrals. -/
noncomputable def regularPowerZeroWeight (F : ℂ → ℂ) (p : ℝ) (z : ℂ) : ℝ :=
  (analyticOrderNatAt F z : ℝ) / (1 + ‖z‖) ^ p

/-- Every power-regularized multiplicity weight is nonnegative.
The numerator and the real-power denominator are nonnegative.
This permits finite-sum tests for summability. -/
theorem regularPowerZeroWeight_nonneg (F : ℂ → ℂ) (p : ℝ) (z : ℂ) :
    0 ≤ regularPowerZeroWeight F p z :=
  div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) _)

/-- For finite points in a ball and a positive denominator lower bound q,
the power-weight sum is at most the ball divisor count divided by q.
Compare summands and use the finite-support divisor total. -/
theorem sum_regularPowerZeroWeight_le_count {F : ℂ → ℂ} (hF : Differentiable ℂ F) (p : ℝ) {R q : ℝ}
    (hq : 0 < q) (t : Finset ℂ) (hm : ∀ z ∈ t, z ∈ Metric.closedBall 0 R)
    (hd : ∀ z ∈ t, q ≤ (1 + ‖z‖) ^ p) :
    (∑ z ∈ t, regularPowerZeroWeight F p z) ≤
      (∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ)) / q := by
  have hb :
    ∀ z ∈ t,
      regularPowerZeroWeight F p z ≤
        (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ) / q := by
    intro z hz
    rw [divisor_closedBall_eq_order hF (hm z hz), Int.cast_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hq (hd z hz)
  have hs := Finset.sum_le_sum hb
  rw [← Finset.sum_div] at hs
  exact hs.trans (div_le_div_of_nonneg_right (sum_divisor_le_finsum hF R t) hq.le)

/-- For p ≥ 0, the inner dyadic shell's power weights are bounded by the divisor
count in the radius-two ball. Their denominators are at least one.
This separates the finite inner contribution from the geometric outer shells. -/
theorem sum_regularPowerZeroWeight_inner_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {p : ℝ}
    (hp : 0 ≤ p) (t : Finset ℂ) (ht : ∀ z ∈ t, zeroMassShell z = 0) :
    (∑ z ∈ t, regularPowerZeroWeight F p z) ≤
      ∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 2) z : ℝ) := by
  have hs :=
    sum_regularPowerZeroWeight_le_count hF p (R := 2) (q := 1) zero_lt_one t
      (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_lt_two_of_zeroMassShell_zero (ht z hz)).le)
      (fun z _ ↦ Real.one_le_rpow (le_add_of_nonneg_right (norm_nonneg z)) hp)
  simpa only [div_one] using hs

/-- Dyadic growth of nonnegative exponent r divided by the shell radius to power p
is bounded by a geometric term with ratio 2^(r-p).
Bound the growth radius by 2^(k+3) and combine the real powers. -/
theorem dyadic_power_order_ratio {r p : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ((2 : ℝ) ^ (k + 2) + 1) ^ r / (2 ^ p) ^ k ≤ 2 ^ (3 * r) * (2 ^ (r - p)) ^ k := by
  have hbase : (2 : ℝ) ^ (k + 2) + 1 ≤ 2 ^ (k + 3) := by
    have hpow : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num only)
    have he : (2 : ℝ) ^ (k + 3) = 2 ^ (k + 2) * 2 := by
      rw [show k + 3 = (k + 2) + 1 by ring]
      exact pow_succ 2 (k + 2)
    rw [he]
    linarith only [hpow]
  have hp := Real.rpow_le_rpow (add_nonneg (pow_nonneg (by norm_num only) _) zero_le_one) hbase hr
  apply (div_le_div_of_nonneg_right hp (pow_nonneg (Real.rpow_nonneg zero_le_two p) k)).trans_eq
  rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 2)]
  rw [show ((k + 3 : ℕ) : ℝ) * r = 3 * r + (k : ℝ) * r by
      simp only [Nat.cast_add, Nat.cast_ofNat]; ring]
  rw [Real.rpow_add (by norm_num only : (0 : ℝ) < 2), mul_comm (k : ℝ) r,
    Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 2) r (k : ℝ), Real.rpow_natCast]
  rw [Real.rpow_sub (by norm_num only : (0 : ℝ) < 2), div_pow]
  ring

/-- The geometric bound for a dyadic shell's power-weighted zero count.
It records the growth constant C, growth exponent r, weight exponent p and the value at zero.
The ratios 2^(r-p) and 2^(-p) are below one when 0 < p and r < p. -/
noncomputable def powerZeroShellMajorant (F : ℂ → ℂ) (C r p : ℝ) (k : ℕ) : ℝ :=
  (C * 2 ^ (3 * r) * (2 ^ (r - p)) ^ k + |Real.log ‖F 0‖| * (2 ^ (-p)) ^ k) / Real.log 2

/-- For C ≥ 0 each geometric shell majorant is nonnegative.
All real-power factors are nonnegative and log 2 is positive.
This allows finite shell sums to be bounded by their total series. -/
theorem powerZeroShellMajorant_nonneg (F : ℂ → ℂ) {C r p : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ powerZeroShellMajorant F C r p k := by
  exact
    div_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg zero_le_two _))
          (pow_nonneg (Real.rpow_nonneg zero_le_two _) _))
        (mul_nonneg (abs_nonneg _) (pow_nonneg (Real.rpow_nonneg zero_le_two _) _)))
      (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le

/-- For 0 < p and r < p the power shell majorant is summable.
Both geometric ratios lie below one.
This is the outer-shell convergence estimate for power-weighted zeros. -/
theorem summable_powerZeroShellMajorant (F : ℂ → ℂ) (C : ℝ) {r p : ℝ} (hp : 0 < p) (hr : r < p) :
    Summable (powerZeroShellMajorant F C r p) := by
  have hq : (2 : ℝ) ^ (r - p) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num only) (sub_neg.mpr hr)
  exact
    (((summable_geometric_of_lt_one (Real.rpow_nonneg zero_le_two _) hq).mul_left
              (C * 2 ^ (3 * r))).add
          ((summable_geometric_of_lt_one (Real.rpow_nonneg zero_le_two _)
                (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num only) (neg_neg_of_pos hp))).mul_left
            |Real.log ‖F 0‖|)).div_const
      _

/-- For an entire function nonzero at zero with an exponential power bound,
a nonzero dyadic shell's p-weight sum is bounded by its geometric majorant.
Apply Jensen's count and the shell's norm lower bound, then simplify the growth ratio. -/
theorem sum_regularPowerZeroWeight_shell_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C r p : ℝ} (hC : 0 < C) (hr : 0 ≤ r) (hp : 0 ≤ p)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) {k : ℕ} (hk : k ≠ 0) (t : Finset ℂ)
    (ht : ∀ z ∈ t, zeroMassShell z = k) :
    (∑ z ∈ t, regularPowerZeroWeight F p z) ≤ powerZeroShellMajorant F C r p k := by
  have hden : ((2 : ℝ) ^ p) ^ k = ((2 : ℝ) ^ k) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, mul_comm p (k : ℝ),
      Real.rpow_natCast_mul zero_le_two]
  have hs :=
    sum_regularPowerZeroWeight_le_count hF p (R := (2 : ℝ) ^ (k + 1)) (q := ((2 : ℝ) ^ p) ^ k)
      (pow_pos (Real.rpow_pos_of_pos zero_lt_two _) _) t
      (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (zeroMassShell_bounds hk (ht z hz)).2.le)
      (fun z hz ↦ by
        rw [hden]
        exact
          Real.rpow_le_rpow (pow_nonneg zero_le_two _)
            ((zeroMassShell_bounds hk (ht z hz)).1.trans (le_add_of_nonneg_left zero_le_one)) hp)
  have hc := jensen_count_le hF h0 hC (pow_pos zero_lt_two (k + 1)) hg
  have he : (2 : ℝ) * 2 ^ (k + 1) = 2 ^ (k + 2) := by
    calc
      (2 : ℝ) * 2 ^ (k + 1) = 2 ^ (k + 1) * 2 := mul_comm _ _
      _ = 2 ^ ((k + 1) + 1) := (pow_succ 2 (k + 1)).symm
      _ = _ := by rw [show (k + 1) + 1 = k + 2 by ring]
  rw [he] at hc
  have hq := div_le_div_of_nonneg_right hc (pow_nonneg (Real.rpow_nonneg zero_le_two p) k)
  have hratio := mul_le_mul_of_nonneg_left (dyadic_power_order_ratio (p := p) hr k) hC.le
  have hlog :=
    div_le_div_of_nonneg_right (neg_le_abs (Real.log ‖F 0‖))
      (pow_nonneg (Real.rpow_nonneg zero_le_two p) k)
  have hgeom : ((2 : ℝ) ^ (-p)) ^ k = 1 / ((2 : ℝ) ^ p) ^ k := by
    rw [Real.rpow_neg zero_le_two, inv_pow, one_div]
  calc
    _ ≤ (C * ((2 : ℝ) ^ (k + 2) + 1) ^ r - Real.log ‖F 0‖) / Real.log 2 / ((2 : ℝ) ^ p) ^ k :=
      hs.trans hq
    _ =
        (C * (((2 : ℝ) ^ (k + 2) + 1) ^ r / ((2 : ℝ) ^ p) ^ k) +
            (-Real.log ‖F 0‖) / ((2 : ℝ) ^ p) ^ k) /
          Real.log 2 :=
      by ring
    _ ≤
        (C * (2 ^ (3 * r) * (2 ^ (r - p)) ^ k) + |Real.log ‖F 0‖| / ((2 : ℝ) ^ p) ^ k) /
          Real.log 2 :=
      div_le_div_of_nonneg_right (add_le_add hratio hlog)
        (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le
    _ = _ := by
      rw [powerZeroShellMajorant, hgeom]; ring

/-- For an entire function nonzero at zero, exponential growth exponent 0 ≤ r < p
with p > 0 implies summability of multiplicities divided by (1+norm z)^p.
Partition finite sums into dyadic shells; Jensen bounds the inner count and the outer
majorants are geometric. This strengthens inverse-square mass when r < p < 2. -/
theorem summable_regularPowerZeroWeight {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C r p : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hp : 0 < p) (hrp : r < p)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) :
    Summable (regularPowerZeroWeight F p) := by
  classical
  let B : ℝ := ∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 2) z : ℝ)
  let g : ℕ → ℝ := powerZeroShellMajorant F C r p
  have hs : Summable g := summable_powerZeroShellMajorant F C hp hrp
  have hn : ∀ k, 0 ≤ g k := powerZeroShellMajorant_nonneg F hC.le
  apply summable_of_sum_le (regularPowerZeroWeight_nonneg F p) (c := B + ∑' k, g k)
  intro t
  rw [← Finset.sum_filter_add_sum_filter_not t (fun z ↦ zeroMassShell z = 0)]
  have hi : (∑ z ∈ t.filter (fun z ↦ zeroMassShell z = 0), regularPowerZeroWeight F p z) ≤ B :=
    sum_regularPowerZeroWeight_inner_le hF hp.le _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)
  let u := t.filter (fun z ↦ ¬zeroMassShell z = 0)
  let v := u.image zeroMassShell
  have hm : ∀ z ∈ u, zeroMassShell z ∈ v := fun z hz ↦ Finset.mem_image_of_mem _ hz
  have hh : (∑ z ∈ u, regularPowerZeroWeight F p z) ≤ ∑' k, g k := by
    calc
      _ = ∑ k ∈ v, ∑ z ∈ u.filter (fun z ↦ zeroMassShell z = k), regularPowerZeroWeight F p z :=
        (Finset.sum_fiberwise_of_maps_to hm (regularPowerZeroWeight F p)).symm
      _ ≤ ∑ k ∈ v, g k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : k ≠ 0 := by
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
          exact (Finset.mem_filter.mp hz).2
        exact
          sum_regularPowerZeroWeight_shell_le hF h0 hC hr0 hp.le hg hk0 _
            (fun z hz ↦ (Finset.mem_filter.mp hz).2)
      _ ≤ _ := hs.sum_le_tsum v (fun k _ ↦ hn k)
  exact add_le_add hi hh

end PseudoPrime.AnalyticNumberTheory.General
