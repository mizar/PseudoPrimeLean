/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.AnalyticMultiplicity
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Inverse-square zero mass from subquadratic entire growth

Jensen's inequality and dyadic shell estimates yield convergence of the
regularized multiplicity weights of an entire function.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an entire F, every finite sum of its nonnegative ball divisor is bounded
by its finite-support total. Enlarge the finite set by the divisor support. -/
theorem sum_divisor_le_finsum {F : ℂ → ℂ} (hF : Differentiable ℂ F) (R : ℝ) (t : Finset ℂ) :
    (∑ z ∈ t, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ)) ≤
      ∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ) := by
  classical
  let D := MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)
  have hf := D.finiteSupport (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have ha : AnalyticOnNhd ℂ F (Metric.closedBall 0 R) := fun z _ ↦ hF.analyticAt z
  have hn : ∀ z, (0 : ℝ) ≤ (D z : ℝ) := fun z ↦ by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha z
  have hsub : Function.support (fun z : ℂ ↦ (D z : ℝ)) ⊆ ↑hf.toFinset := by
    intro z hz
    exact
      hf.mem_toFinset.mpr
        (fun h ↦
          hz
            (by
              change (D z : ℝ) = 0; rw [h, Int.cast_zero]))
  rw [show
      (∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ)) =
        ∑ z ∈ hf.toFinset, (D z : ℝ)
      from finsum_eq_sum_of_support_subset (fun z ↦ (D z : ℝ)) hsub]
  have hle : (∑ z ∈ t, (D z : ℝ)) ≤ ∑ z ∈ t ∪ hf.toFinset, (D z : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ hn z)
  have he : (∑ z ∈ t ∪ hf.toFinset, (D z : ℝ)) = ∑ z ∈ hf.toFinset, (D z : ℝ) := by
    symm
    apply Finset.sum_subset Finset.subset_union_right
    intro z _ hz
    have hzero : D z = 0 := by
      by_contra hne
      exact hz (hf.mem_toFinset.mpr hne)
    rw [hzero, Int.cast_zero]
  exact hle.trans_eq he

/-- For an entire F and a point in the closed ball, its ball divisor equals its
natural analytic multiplicity. Separate finite and infinite analytic orders. -/
theorem divisor_closedBall_eq_order {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R : ℝ} {z : ℂ}
    (hz : z ∈ Metric.closedBall 0 R) :
    MeromorphicOn.divisor F (Metric.closedBall 0 R) z = (analyticOrderNatAt F z : ℤ) := by
  have ha : AnalyticOnNhd ℂ F (Metric.closedBall 0 R) := fun z _ ↦ hF.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha hz, analyticOrderNatAt]
  induction analyticOrderAt F z using ENat.recTopCoe <;> rfl

/-- For entire F with F(0) nonzero and a global exponential power bound, Jensen's
inequality bounds the multiplicity count inside radius R by the growth at 2R.
The explicit logarithmic denominator supports summability of zero weights. -/
theorem jensen_count_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r R : ℝ}
    (hC : 0 < C) (hR : 0 < R) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) :
    (∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ)) ≤
      (C * (2 * R + 1) ^ r - Real.log ‖F 0‖) / Real.log 2 := by
  have ha : AnalyticOnNhd ℂ F (Metric.closedBall 0 |2 * R|) := fun z _ ↦ hF.analyticAt z
  have hb : ∀ z ∈ Metric.sphere (0 : ℂ) |2 * R|, ‖F z‖ ≤ Real.exp (C * (2 * R + 1) ^ r) := by
    intro z hz
    have he : ‖z‖ = 2 * R := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos (mul_pos zero_lt_two hR)] using hz
    simpa only [he] using hg z
  have hj :=
    AnalyticOnNhd.sum_divisor_le (c := (0 : ℂ)) (r := R) (R := 2 * R) (by rwa [abs_of_pos hR])
      (by
        rw [abs_of_pos hR, abs_of_pos (mul_pos zero_lt_two hR)]; linarith only [hR])
      (Real.one_le_exp (mul_nonneg hC.le (Real.rpow_nonneg (by linarith only [hR]) _))) ha h0 hb
  rw [abs_of_pos hR, show 2 * R / R = (2 : ℝ) from mul_div_cancel_right₀ 2 hR.ne'] at hj
  have hf :=
    (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)).finiteSupport
      (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  have he :
    ((∑ᶠ z : ℂ, MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℤ) : ℝ) =
      ∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ) :=
    (Int.castRingHom ℝ).toAddMonoidHom.map_finsum hf
  rw [he, Real.log_div (Real.exp_pos _).ne' (norm_pos_iff.mpr h0).ne', Real.log_exp] at hj
  exact hj

/-- The dyadic radial shell index, with the inner region of norm below two at index zero.
Nonzero indices bound the norm between successive powers of two. -/
noncomputable def zeroMassShell (z : ℂ) : ℕ :=
  ⌊Real.logb 2 ‖z‖⌋₊

/-- A point in the innermost dyadic shell has norm below two.
Use the natural floor bound for its base-two logarithm. -/
theorem norm_lt_two_of_zeroMassShell_zero {z : ℂ} (hz : zeroMassShell z = 0) : ‖z‖ < 2 := by
  rw [zeroMassShell, Nat.floor_eq_zero] at hz
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · rw [← h0]
    norm_num only
  · rw [Real.logb_lt_iff_lt_rpow (by norm_num only) h0, Real.rpow_one] at hz
    exact hz

/-- For a nonzero dyadic shell index k, the norm lies between 2^k and 2^(k+1).
The lower and upper natural-floor bounds give the annular estimates. -/
theorem zeroMassShell_bounds {z : ℂ} {k : ℕ} (hk : k ≠ 0) (hz : zeroMassShell z = k) :
    (2 : ℝ) ^ k ≤ ‖z‖ ∧ ‖z‖ < 2 ^ (k + 1) := by
  have hp : 0 < ‖z‖ := by
    by_contra hn
    have he : ‖z‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg z)
    rw [zeroMassShell, he, Real.logb_zero, Nat.floor_zero] at hz
    exact hk hz.symm
  have hlo : (k : ℝ) ≤ Real.logb 2 ‖z‖ := by
    rw [zeroMassShell] at hz
    exact_mod_cast (Nat.le_floor_iff' hk).mp hz.ge
  have hhi : Real.logb 2 ‖z‖ < ((k + 1 : ℕ) : ℝ) := by
    have hf := Nat.lt_floor_add_one (Real.logb 2 ‖z‖)
    change Real.logb 2 ‖z‖ < (zeroMassShell z : ℝ) + 1 at hf
    simpa only [hz, Nat.cast_add, Nat.cast_one] using hf
  constructor
  · simpa only [Real.rpow_natCast] using (Real.le_logb_iff_rpow_le (by norm_num only) hp).mp hlo
  · simpa only [Real.rpow_natCast] using (Real.logb_lt_iff_lt_rpow (by norm_num only) hp).mp hhi

/-- Analytic multiplicity divided by one plus squared norm.
This nonnegative weight avoids a singular denominator at zero. -/
noncomputable def regularZeroWeight (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (analyticOrderNatAt F z : ℝ) / (1 + ‖z‖ ^ 2)

/-- Every regularized zero weight is nonnegative, since multiplicities and
its denominator are nonnegative. This permits finite-sum convergence criteria. -/
theorem regularZeroWeight_nonneg (F : ℂ → ℂ) (z : ℂ) : 0 ≤ regularZeroWeight F z :=
  div_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (sq_nonneg _))

/-- For entire F, finite points in a ball, and a positive lower denominator q,
bound the sum of regularized zero weights by the ball's divisor count divided by q.
Compare summands and use the finite-support divisor total. -/
theorem sum_regularZeroWeight_le_count {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R q : ℝ} (hq : 0 < q)
    (t : Finset ℂ) (hm : ∀ z ∈ t, z ∈ Metric.closedBall 0 R) (hd : ∀ z ∈ t, q ≤ 1 + ‖z‖ ^ 2) :
    (∑ z ∈ t, regularZeroWeight F z) ≤
      (∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ)) / q := by
  have hb :
    ∀ z ∈ t,
      regularZeroWeight F z ≤ (MeromorphicOn.divisor F (Metric.closedBall 0 R) z : ℝ) / q := by
    intro z hz
    rw [divisor_closedBall_eq_order hF (hm z hz), Int.cast_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hq (hd z hz)
  have hs := Finset.sum_le_sum hb
  rw [← Finset.sum_div] at hs
  exact hs.trans (div_le_div_of_nonneg_right (sum_divisor_le_finsum hF R t) hq.le)

/-- For entire F, bound the weights in the inner dyadic shell by the finite
ball divisor total at radius two. The regularized denominator is at least one. -/
theorem sum_regularZeroWeight_inner_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (t : Finset ℂ)
    (ht : ∀ z ∈ t, zeroMassShell z = 0) :
    (∑ z ∈ t, regularZeroWeight F z) ≤
      ∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 2) z : ℝ) := by
  have hs :=
    sum_regularZeroWeight_le_count hF (R := 2) (q := 1) zero_lt_one t
      (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_lt_two_of_zeroMassShell_zero (ht z hz)).le)
      (fun z _ ↦ le_add_of_nonneg_right (sq_nonneg ‖z‖))
  simpa only [div_one] using hs

/-- For a nonnegative exponent r, bound dyadic growth divided by the squared
shell radius by a geometric term with ratio 2^(r-2). Monotonicity of real powers
and exponent arithmetic give the bound used in the zero-weight series. -/
theorem dyadic_order_ratio {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    ((2 : ℝ) ^ (k + 2) + 1) ^ r / 4 ^ k ≤ 2 ^ (3 * r) * (2 ^ (r - 2)) ^ k := by
  have hbase : (2 : ℝ) ^ (k + 2) + 1 ≤ 2 ^ (k + 3) := by
    have hpow : (1 : ℝ) ≤ 2 ^ (k + 2) := one_le_pow₀ (by norm_num only)
    have he : (2 : ℝ) ^ (k + 3) = 2 ^ (k + 2) * 2 := by
      rw [show k + 3 = (k + 2) + 1 by ring]
      exact pow_succ 2 (k + 2)
    rw [he]
    linarith only [hpow]
  have hp := Real.rpow_le_rpow (add_nonneg (pow_nonneg (by norm_num only) _) zero_le_one) hbase hr
  apply (div_le_div_of_nonneg_right hp (pow_nonneg (by norm_num only) k)).trans_eq
  rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 2)]
  rw [show ((k + 3 : ℕ) : ℝ) * r = 3 * r + (k : ℝ) * r by
      simp only [Nat.cast_add, Nat.cast_ofNat]; ring]
  rw [Real.rpow_add (by norm_num only : (0 : ℝ) < 2), mul_comm (k : ℝ) r,
    Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 2) r (k : ℝ), Real.rpow_natCast]
  rw [Real.rpow_sub (by norm_num only : (0 : ℝ) < 2), Real.rpow_two, div_pow]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num only]
  ring

/-- The geometric majorant for a dyadic shell's regularized zero mass.
It records the growth coefficient, exponent, and the logarithmic value at zero. -/
noncomputable def zeroShellMajorant (F : ℂ → ℂ) (C r : ℝ) (k : ℕ) : ℝ :=
  (C * 2 ^ (3 * r) * (2 ^ (r - 2)) ^ k + |Real.log ‖F 0‖| * (1 / 4 : ℝ) ^ k) / Real.log 2

/-- For a nonnegative growth coefficient, every shell majorant is nonnegative.
All factors are nonnegative and log two is positive. -/
theorem zeroShellMajorant_nonneg (F : ℂ → ℂ) {C r : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ zeroShellMajorant F C r k := by
  exact
    div_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg zero_le_two _))
          (pow_nonneg (Real.rpow_nonneg zero_le_two _) _))
        (mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num only) _)))
      (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le

/-- For r < 2 and arbitrary F and C, the dyadic shell majorant is summable.
Both geometric ratios are below one. This supplies the outer-shell convergence
estimate; applying it to zero mass additionally requires the entire-function growth bound. -/
theorem summable_zeroShellMajorant (F : ℂ → ℂ) (C : ℝ) {r : ℝ} (hr : r < 2) :
    Summable (zeroShellMajorant F C r) := by
  have hq : (2 : ℝ) ^ (r - 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num only) (sub_neg.mpr hr)
  exact
    (((summable_geometric_of_lt_one (Real.rpow_nonneg zero_le_two _) hq).mul_left
              (C * 2 ^ (3 * r))).add
          ((summable_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 1 / 4)
                (by norm_num only : (1 / 4 : ℝ) < 1)).mul_left
            |Real.log ‖F 0‖|)).div_const
      _

/-- For entire F nonzero at zero, a global exponential power bound with
nonnegative exponent controls the finite weight sum in each nonzero shell.
Combine Jensen's count, the inverse-square denominator, and the geometric ratio. -/
theorem sum_regularZeroWeight_shell_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C r : ℝ} (hC : 0 < C) (hr : 0 ≤ r) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) {k : ℕ}
    (hk : k ≠ 0) (t : Finset ℂ) (ht : ∀ z ∈ t, zeroMassShell z = k) :
    (∑ z ∈ t, regularZeroWeight F z) ≤ zeroShellMajorant F C r k := by
  have hfour : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num only
  have hs :=
    sum_regularZeroWeight_le_count hF (R := (2 : ℝ) ^ (k + 1)) (q := (4 : ℝ) ^ k)
      (pow_pos (by norm_num only) _) t
      (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (zeroMassShell_bounds hk (ht z hz)).2.le)
      (fun z hz ↦ by
        have hl := (zeroMassShell_bounds hk (ht z hz)).1
        have hp := mul_le_mul hl hl (pow_nonneg zero_le_two k) (norm_nonneg z)
        have hpsq : ((2 : ℝ) ^ k) ^ 2 ≤ ‖z‖ ^ 2 := by simpa only [pow_two] using hp
        rw [hfour]
        exact hpsq.trans (le_add_of_nonneg_left zero_le_one))
  have hc := jensen_count_le hF h0 hC (pow_pos zero_lt_two (k + 1)) hg
  have he : (2 : ℝ) * 2 ^ (k + 1) = 2 ^ (k + 2) := by
    calc
      (2 : ℝ) * 2 ^ (k + 1) = 2 ^ (k + 1) * 2 := mul_comm _ _
      _ = 2 ^ ((k + 1) + 1) := (pow_succ 2 (k + 1)).symm
      _ = _ := by rw [show (k + 1) + 1 = k + 2 by ring]
  rw [he] at hc
  have hq := div_le_div_of_nonneg_right hc (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 4) k)
  have hratio := mul_le_mul_of_nonneg_left (dyadic_order_ratio hr k) hC.le
  have hlog :=
    div_le_div_of_nonneg_right (neg_le_abs (Real.log ‖F 0‖))
      (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 4) k)
  have hgeom : (1 / 4 : ℝ) ^ k = 1 / (4 : ℝ) ^ k := by rw [div_pow, one_pow]
  calc
    _ ≤ (C * ((2 : ℝ) ^ (k + 2) + 1) ^ r - Real.log ‖F 0‖) / Real.log 2 / (4 : ℝ) ^ k := hs.trans hq
    _ =
        (C * (((2 : ℝ) ^ (k + 2) + 1) ^ r / (4 : ℝ) ^ k) + (-Real.log ‖F 0‖) / (4 : ℝ) ^ k) /
          Real.log 2 :=
      by ring
    _ ≤ (C * (2 ^ (3 * r) * (2 ^ (r - 2)) ^ k) + |Real.log ‖F 0‖| / (4 : ℝ) ^ k) / Real.log 2 :=
      div_le_div_of_nonneg_right (add_le_add hratio hlog)
        (Real.log_pos (by norm_num only : (1 : ℝ) < 2)).le
    _ = _ := by
      rw [zeroShellMajorant, hgeom]; ring

/-- For entire F nonzero at zero, an exponential power bound with exponent
between zero and two implies summability of regularized zero weights.
Partition finite sums into dyadic shells; the inner count is finite and the
outer majorants form a convergent geometric series. -/
theorem summable_regularZeroWeight {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) {C r : ℝ}
    (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2) (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) :
    Summable (regularZeroWeight F) := by
  classical
  let B : ℝ := ∑ᶠ z : ℂ, (MeromorphicOn.divisor F (Metric.closedBall 0 2) z : ℝ)
  let g : ℕ → ℝ := zeroShellMajorant F C r
  have hs : Summable g := summable_zeroShellMajorant F C hr2
  have hn : ∀ k, 0 ≤ g k := zeroShellMajorant_nonneg F hC.le
  apply summable_of_sum_le (regularZeroWeight_nonneg F) (c := B + ∑' k, g k)
  intro t
  rw [← Finset.sum_filter_add_sum_filter_not t (fun z ↦ zeroMassShell z = 0)]
  have hi : (∑ z ∈ t.filter (fun z ↦ zeroMassShell z = 0), regularZeroWeight F z) ≤ B :=
    sum_regularZeroWeight_inner_le hF _ (fun z hz ↦ (Finset.mem_filter.mp hz).2)
  let u := t.filter (fun z ↦ ¬zeroMassShell z = 0)
  let v := u.image zeroMassShell
  have hm : ∀ z ∈ u, zeroMassShell z ∈ v := fun z hz ↦ Finset.mem_image_of_mem _ hz
  have hh : (∑ z ∈ u, regularZeroWeight F z) ≤ ∑' k, g k := by
    calc
      _ = ∑ k ∈ v, ∑ z ∈ u.filter (fun z ↦ zeroMassShell z = k), regularZeroWeight F z :=
        (Finset.sum_fiberwise_of_maps_to hm (regularZeroWeight F)).symm
      _ ≤ ∑ k ∈ v, g k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : k ≠ 0 := by
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
          exact (Finset.mem_filter.mp hz).2
        exact
          sum_regularZeroWeight_shell_le hF h0 hC hr0 hg hk0 _
            (fun z hz ↦ (Finset.mem_filter.mp hz).2)
      _ ≤ _ := hs.sum_le_tsum v (fun k _ ↦ hn k)
  exact add_le_add hi hh

end PseudoPrime.AnalyticNumberTheory.General
