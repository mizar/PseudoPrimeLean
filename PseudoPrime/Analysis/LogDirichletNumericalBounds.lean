/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerIntegralBounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-! # A sharper logarithmic Dirichlet numerator bound

The pure logarithmic integrand is decreasing past three. Treating its first two terms
separately improves the additive allowance from 1/r to 1/(r+1).
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At positive x, the derivative of log x times x^(-r-1) is x^(-r-2) times
1-(r+1)log x. Differentiate both factors and normalize powers. Its sign controls
the logarithmic Dirichlet tail. -/
theorem hasDerivAt_logPower {r x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ Real.log t * t ^ (-r - 1)) (x ^ (-r - 2) * (1 - (r + 1) * Real.log x))
      x := by
  have hd :=
    (Real.hasDerivAt_log hx.ne').mul (Real.hasDerivAt_rpow_const (Or.inl hx.ne') (p := -r - 1))
  have he :
    x⁻¹ * x ^ (-r - 1) + Real.log x * ((-r - 1) * x ^ (-r - 1 - 1)) =
      x ^ (-r - 2) * (1 - (r + 1) * Real.log x) := by
    rw [show -r - 2 = (-r - 1) - 1 by ring, Real.rpow_sub_one hx.ne' (-r - 1)]
    ring
  exact he ▸ hd

/-- For positive r, log x times x^(-r-1) decreases on [3,infinity]. The derivative
is nonpositive because log three exceeds one. This avoids imposing monotonicity
on the first two nonzero terms of the series. -/
theorem antitoneOn_logPower_three {r : ℝ} (hr : 0 < r) :
    AntitoneOn (fun x : ℝ ↦ Real.log x * x ^ (-r - 1)) (Set.Ici 3) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3)
      (fun x hx ↦
        (hasDerivAt_logPower (r := r)
            (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 3) hx)).continuousAt.continuousWithinAt)
      (fun x hx ↦
        (hasDerivAt_logPower
            (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 3)
              (interior_subset hx))).hasDerivWithinAt)
  intro x hx
  have hx3 : 3 ≤ x := interior_subset hx
  have hl := (Real.log_le_log (by norm_num only : (0 : ℝ) < 3) hx3).trans' Real.log_three_gt_d9.le
  have hb : 1 - (r + 1) * Real.log x ≤ 0 := by nlinarith only [hr, hl]
  exact
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ((by norm_num only : (0 : ℝ) ≤ 3).trans hx3) _)
      hb

/-- For positive r, the pure logarithmic-power integrand is integrable from one
to infinity. Dominate its nonnegative values by the established envelope with
log x+1. This justifies the sharper integral comparison. -/
theorem integrableOn_logPower {r : ℝ} (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.log x * x ^ (-r - 1)) (Set.Ioi 1) := by
  apply (integrableOn_logPower_envelope hr).mono'
  · have hc : ContinuousOn (fun x : ℝ ↦ Real.log x * x ^ (-r - 1)) (Set.Ioi 1) := fun x hx ↦
      (hasDerivAt_logPower (lt_trans zero_lt_one hx)).continuousAt.continuousWithinAt
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg
        (mul_nonneg (Real.log_nonneg hx.le) (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _))]
    exact
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)

/-- For positive r, the integral of log x times x^(-r-1) from one to infinity
is r^(-2). Subtract the pure-power integral from the envelope integral. This
retains only the main integral in the zeta derivative numerator. -/
theorem integral_logPower {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Set.Ioi 1, Real.log x * x ^ (-r - 1)) = r⁻¹ ^ 2 := by
  have he := integral_logPower_envelope hr
  have hpow := integrableOn_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) zero_lt_one
  have hval := integral_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) zero_lt_one
  have hf :
    (fun x : ℝ ↦ (Real.log x + 1) * x ^ (-r - 1)) =
      (fun x : ℝ ↦ Real.log x * x ^ (-r - 1) + x ^ (-r - 1)) := by
    ext x
    ring
  rw [hf, MeasureTheory.integral_add (integrableOn_logPower hr) hpow] at he
  norm_num only [Real.one_rpow] at hval
  have hv : (∫ x : ℝ in Set.Ioi 1, x ^ (-r - 1)) = r⁻¹ := by
    rw [hval]
    rw [show -r - 1 + 1 = -r by ring, div_neg, neg_div, neg_neg, one_div]
  rw [hv] at he
  linarith only [he]

/-- For positive sigma and x at least one, log x times x^(-sigma) is at most
1/(2 sigma). Apply the exponential tangent inequality and exp(1)>2. This
bounds each of the first two nonzero series terms without rational power evaluation. -/
theorem logPower_le_half_inv {σ x : ℝ} (hσ : 0 < σ) (hx : 1 ≤ x) :
    Real.log x * x ^ (-σ) ≤ 1 / (2 * σ) := by
  have hx0 := zero_lt_one.trans_le hx
  have hu : 0 ≤ σ * Real.log x := mul_nonneg hσ.le (Real.log_nonneg hx)
  have h := Real.add_one_le_exp (σ * Real.log x - 1)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(σ * Real.log x))).le
  have he : Real.exp (σ * Real.log x - 1) * Real.exp (-(σ * Real.log x)) = Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hm
  have hex : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 2) Real.exp_one_gt_two.le
  rw [Real.rpow_def_of_pos hx0]
  have heq : Real.log x * -σ = -(σ * Real.log x) := by ring
  rw [heq]
  apply (le_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) hσ)).mpr
  nlinarith only [hm, hex]

/-- For positive r, the logarithmic Dirichlet series is at most r^(-2)+1/(r+1).
Compare the terms from four onward with the integral from three, then bound the
two remaining terms by 1/(2(r+1)) each. This unconditional numerator estimate
supports a smaller Euler-ratio allowance in the Gamma zero-mass comparison. -/
theorem tsum_logPower_le {r : ℝ} (hr : 0 < r) :
    (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-r - 1)) ≤ r⁻¹ ^ 2 + (r + 1)⁻¹ := by
  have hi := integrableOn_logPower hr
  have hsub : Set.Ioi (3 : ℝ) ⊆ Set.Ioi 1 := fun x hx ↦ lt_trans (by norm_num only : (1 : ℝ) < 3) hx
  have hn (x : ℝ) (hx : x ∈ Set.Ioi (1 : ℝ)) : 0 ≤ Real.log x * x ^ (-r - 1) :=
    mul_nonneg (Real.log_nonneg hx.le) (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)
  have hi3 := hi.mono_set hsub
  have ha := antitoneOn_logPower_three hr
  have hs :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := 3) (by simpa only [Nat.cast_ofNat] using ha)
      (by simpa only [Nat.cast_ofNat] using hi3) (fun x hx ↦ hn x (hsub hx))
  have ht :=
    AntitoneOn.tsum_comp_add_le_integral 3 (by simpa only [Nat.cast_ofNat] using ha)
      (by simpa only [Nat.cast_ofNat] using hi3) (fun x hx ↦ hn x (hsub hx))
  have him :=
    MeasureTheory.setIntegral_mono_set hi
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        exact hn x hx)
      (Filter.Eventually.of_forall hsub)
  rw [integral_logPower hr] at him
  have hsum := hs.sum_add_tsum_nat_add 4
  have h2 :=
    logPower_le_half_inv (by linarith only [hr] : 0 < r + 1) (by norm_num only : (1 : ℝ) ≤ 2)
  have h3 :=
    logPower_le_half_inv (by linarith only [hr] : 0 < r + 1) (by norm_num only : (1 : ℝ) ≤ 3)
  rw [show -(r + 1) = -r - 1 by ring] at h2 h3
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, Real.log_zero, Real.log_one, zero_mul, zero_add, add_zero] at hsum
  have htail : (∑' n : ℕ, Real.log (n + 4 : ℕ) * (n + 4 : ℕ) ^ (-r - 1)) ≤ r⁻¹ ^ 2 := by
    have ht' :
      (∑' n : ℕ, Real.log (n + 4 : ℕ) * (n + 4 : ℕ) ^ (-r - 1)) ≤
        ∫ x : ℝ in Set.Ioi 3, Real.log x * x ^ (-r - 1) := by
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_ofNat] using ht
    exact ht'.trans him
  rw [← hsum]
  simp only [one_div] at h2 h3
  have he : (2 * (r + 1))⁻¹ = (r + 1)⁻¹ / 2 := by rw [mul_inv, div_eq_mul_inv, mul_comm]
  rw [he] at h2 h3
  linarith only [htail, h2, h3]

/-- For positive r and positive cutoff c, x^(-r-1) decreases on [c,infinity].
Use the order rule for nonpositive real exponents. This supplies the denominator
integral comparison for the Euler ratio. -/
theorem antitoneOn_neg_rpow {r : ℝ} (hr : 0 < r) {c : ℝ} (hc : 0 < c) :
    AntitoneOn (fun x : ℝ ↦ x ^ (-r - 1)) (Set.Ici c) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (hc.trans_le hx) hxy (by linarith only [hr])

/-- For positive r, the natural-number series n^(-r-1) is summable. Apply the
integral test beyond one; finitely many initial terms do not affect convergence.
This permits exact separation of the term at one. -/
theorem summable_neg_rpow {r : ℝ} (hr : 0 < r) : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-r - 1)) := by
  exact
    AntitoneOn.summable_of_integrableOn_Ioi (N := 1) (f := fun x : ℝ ↦ x ^ (-r - 1))
      (by simpa only [Nat.cast_one] using antitoneOn_neg_rpow hr zero_lt_one)
      (by
        simpa only [Nat.cast_one] using
          integrableOn_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) zero_lt_one)
      (fun x hx ↦
        Real.rpow_nonneg
          (((show (0 : ℝ) < (1 : ℕ) from Nat.cast_pos.mpr Nat.zero_lt_one).trans hx).le) _)

/-- For positive r, the power Dirichlet series is at least 1+2^(-r)/r.
Keep its term at one and bound the tail from two below by its integral. This
retains a nontrivial denominator in the ordinary logarithmic-derivative bound. -/
theorem one_add_two_rpow_div_le_tsum {r : ℝ} (hr : 0 < r) :
    1 + (2 : ℝ) ^ (-r) / r ≤ ∑' n : ℕ, (n : ℝ) ^ (-r - 1) := by
  have h :=
    AntitoneOn.integral_le_tsum_comp_add (f := fun x : ℝ ↦ x ^ (-r - 1)) 2
      (by simpa only [Nat.cast_ofNat] using antitoneOn_neg_rpow hr (by norm_num only : (0 : ℝ) < 2))
      (summable_neg_rpow hr)
      (fun x hx ↦ Real.rpow_nonneg (lt_trans (by norm_num only : (0 : ℝ) < 2) hx).le _)
  have hi :=
    integral_Ioi_rpow_of_lt (by linarith only [hr] : -r - 1 < -1) (by norm_num only : (0 : ℝ) < 2)
  rw [show -r - 1 + 1 = -r by ring, div_neg, neg_div, neg_neg] at hi
  norm_num only [Nat.cast_ofNat] at h
  rw [hi] at h
  have he := (summable_neg_rpow hr).sum_add_tsum_nat_add 2
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    Real.zero_rpow (by linarith only [hr] : -r - 1 ≠ 0), Real.one_rpow, zero_add] at he
  rw [← he]
  linarith only [h]

/-- A nonnegative d with d^20 times 2^m at most one is at most 2^(-m/20).
Compare twentieth powers and use the real-power multiplication rule. This turns
small rational data into certified lower bounds for Euler-ratio denominators. -/
theorem le_two_rpow_neg_twentieth {d : ℝ} (hd : 0 ≤ d) (m : ℕ) (hcheck : d ^ 20 * (2 : ℝ) ^ m ≤ 1) :
    d ≤ (2 : ℝ) ^ (-(m : ℝ) / 20) := by
  have hpow : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num only) _
  have ht : d ^ 20 ≤ ((2 : ℝ) ^ m)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hpow).mpr hcheck
  apply
    (pow_le_pow_iff_left₀ hd (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) _)
        (by decide : (20 : ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (by norm_num only : (0 : ℝ) ≤ 2)]
  norm_num only [Nat.cast_ofNat]
  rw [show -(m : ℝ) / 20 * 20 = -(m : ℝ) by ring, Real.rpow_neg (by norm_num only : (0 : ℝ) ≤ 2),
    Real.rpow_natCast]
  exact ht

end PseudoPrime.Analysis
