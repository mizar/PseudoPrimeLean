/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform comparison of complex digamma and logarithm

Horizontal logarithmic increments have an inverse-square error majorant.
Their telescoping sum and the Euler series identify digamma minus the principal logarithm,
yielding a bound uniform on the half-plane Re s ≥ 1/2.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- With a positive lower bound on the real part, the error in approximating a unit
logarithmic increment by its initial reciprocal is at most the inverse square of that bound.
Differentiate along the horizontal unit segment and apply the mean value inequality.
This controls each term of the digamma logarithm comparison. -/
private theorem norm_log_add_one_sub_log_sub_reciprocal_le {a : ℂ} {r : ℝ} (hr : 0 < r)
    (ha : r ≤ a.re) : ‖Complex.log (a + 1) - Complex.log a - 1 / a‖ ≤ 1 / r ^ 2 := by
  have hd :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ ↦ Complex.log (a + t) - (t : ℂ) / a) (1 / (a + t) - 1 / a)
        (Set.Icc 0 1) t := by
    intro t ht
    have hslit : a + t ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      apply Or.inl
      rw [Complex.add_re, Complex.ofReal_re]
      exact add_pos_of_pos_of_nonneg (hr.trans_le ha) ht.1
    have hl :=
      (((hasDerivAt_id (t : ℂ)).const_add a).clog hslit).sub ((hasDerivAt_id (t : ℂ)).div_const a)
    simpa only [id_eq, Pi.sub_apply] using hl.comp_ofReal.hasDerivWithinAt
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖1 / (a + t) - 1 / a‖ ≤ 1 / r ^ 2 := by
    intro t ht
    have hn : r ≤ ‖a‖ := ha.trans (Complex.re_le_norm a)
    have hnt : r ≤ ‖a + t‖ := by
      have h := Complex.re_le_norm (a + t)
      rw [Complex.add_re, Complex.ofReal_re] at h
      linarith only [ha, ht.1, h]
    have ha0 : a ≠ 0 := norm_pos_iff.mp (hr.trans_le hn)
    have hat0 : a + t ≠ 0 := norm_pos_iff.mp (hr.trans_le hnt)
    have he : 1 / (a + t) - 1 / a = -(t : ℂ) / ((a + t) * a) := by
      rw [div_sub_div _ _ hat0 ha0]
      congr 1
      ring
    rw [he, norm_div, norm_neg, Complex.norm_of_nonneg ht.1, norm_mul]
    exact
      div_le_div₀ zero_le_one ht.2.le (sq_pos_of_pos hr)
        (by simpa only [pow_two] using mul_le_mul hnt hn hr.le (norm_nonneg (a + t)))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb
  simpa only [Complex.ofReal_one, Complex.ofReal_zero, add_zero, zero_div, sub_zero, sub_sub,
    add_comm (1 / a) (Complex.log a)] using h

/-- For a complex argument and a natural index, the horizontal unit increment of the
principal logarithm minus the initial reciprocal. On the right half-plane these errors
are summable and their sum is digamma minus the principal logarithm. -/
noncomputable def digammaLogError (s : ℂ) (n : ℕ) : ℂ :=
  Complex.log (s + n + 1) - Complex.log (s + n) - 1 / (s + n)

/-- On Re s ≥ 1/2, each logarithmic increment error is bounded by 4/(n+1)².
The horizontal segment stays at real part at least (n+1)/2; apply the unit-segment estimate.
The majorant is independent of the argument and bounds the full digamma error series. -/
theorem norm_digammaLogError_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) :
    ‖digammaLogError s n‖ ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
  have hp : 0 < ((n : ℝ) + 1) / 2 :=
    div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one) (by norm_num only)
  have hr : ((n : ℝ) + 1) / 2 ≤ (s + n).re := by
    rw [Complex.add_re, Complex.natCast_re]
    nlinarith only [hs, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h := norm_log_add_one_sub_log_sub_reciprocal_le hp hr
  have he : 1 / (((n : ℝ) + 1) / 2) ^ 2 = 4 / ((n : ℝ) + 1) ^ 2 := by
    rw [div_pow]
    norm_num only [Nat.reducePow]
    rw [div_div_eq_mul_div, one_mul]
  exact he ▸ h

/-- For Re s ≥ 1/2, the logarithmic increment errors are absolutely summable.
Dominate their norms by the convergent shifted inverse-square series.
This justifies taking limits of their finite telescoping sums. -/
theorem summable_digammaLogError {s : ℂ} (hs : 1 / 2 ≤ s.re) : Summable (digammaLogError s) := by
  have hb : Summable (fun n : ℕ ↦ 4 / ((n : ℝ) + 1) ^ 2) := by
    have h :=
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (show 1 < (2 : ℕ) by decide))
    simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h.mul_left 4
  exact
    summable_norm_iff.mp (hb.of_nonneg_of_le (fun n ↦ norm_nonneg _) (norm_digammaLogError_le hs))

/-- For every complex argument and finite length, the sum of logarithmic increment errors
is the endpoint logarithm difference minus the reciprocal sum. Telescope the logarithms.
This identity connects the error series with the Euler series for digamma. -/
theorem sum_digammaLogError (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, digammaLogError s n =
      Complex.log (s + N) - Complex.log s - ∑ n ∈ Finset.range N, 1 / (s + n) := by
  simp only [digammaLogError, Finset.sum_sub_distrib]
  have h := Finset.sum_range_sub' (fun n : ℕ ↦ Complex.log (s + n)) N
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at h
  have h' := congrArg Neg.neg h
  simpa only [neg_sub, ← Finset.sum_neg_distrib, Finset.sum_sub_distrib, ← add_assoc] using
    congrArg (fun z : ℂ ↦ z - ∑ n ∈ Finset.range N, 1 / (s + n)) h'

/-- For a fixed argument of positive real part, log(s+N) minus the real log(N+1) tends to zero.
Normalize by N+1, use convergence of the resulting ratio to one, and apply continuity of
the principal logarithm there. This removes the logarithmic endpoint in the Euler limit. -/
theorem tendsto_log_shift_sub_log_nat_add_one {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ ↦ Complex.log (s + N) - (Real.log ((N : ℝ) + 1) : ℂ)) Filter.atTop
      (nhds 0) := by
  have hi : Filter.Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
    ((tendsto_natCast_atTop_atTop :
            Filter.Tendsto (fun N : ℕ ↦ (N : ℝ)) Filter.atTop Filter.atTop).atTop_add
        tendsto_const_nhds).inv_tendsto_atTop
  have hq : Filter.Tendsto (fun N : ℕ ↦ (s + N) / ((N : ℂ) + 1)) Filter.atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).add (hi.ofReal.const_mul (s - 1))
    simp only [Complex.ofReal_zero, mul_zero, add_zero] at h
    convert h using 1
    ext N
    have hn : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    rw [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    rw [← div_eq_mul_inv, add_div_eq_mul_add_div _ _ hn]
    congr 1
    ring
  have hlog :=
    (Complex.differentiableAt_log
          (Complex.mem_slitPlane_iff.mpr
            (Or.inl
              (show (0 : ℝ) < (1 : ℂ).re by
                norm_num only [Complex.one_re])))).continuousAt.tendsto.comp
      hq
  simp only [Complex.log_one] at hlog
  convert hlog using 1
  ext N
  have hp : 0 < (N : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg N) zero_lt_one
  have hz : s + N ≠ 0 := by
    apply norm_pos_iff.mp
    apply lt_of_lt_of_le _ (Complex.re_le_norm _)
    rw [Complex.add_re, Complex.natCast_re]
    exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg N)
  have hn : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have h := Complex.log_ofReal_mul hp (div_ne_zero hz hn)
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    mul_div_cancel₀ _ hn] at h
  dsimp only [Function.comp_apply]
  linear_combination h

/-- On Re s ≥ 1/2, digamma minus the principal logarithm is the sum of logarithmic increment
errors. Combine finite telescoping with the Euler digamma series, the harmonic limit defining
Euler's constant, and the normalized logarithmic endpoint limit.
This provides a uniformly summable representation for the archimedean endpoint error. -/
theorem digamma_sub_log_eq_tsum_digammaLogError {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    Complex.digamma s - Complex.log s = ∑' n : ℕ, digammaLogError s n := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hs
  have hh := Real.tendsto_harmonic_sub_log_add_one.ofReal
  simp only [Complex.ofReal_sub, Complex.ofReal_ratCast] at hh
  have hr := (summable_digammaResolvent hs0.le).hasSum.tendsto_sum_nat
  have hlim := ((tendsto_log_shift_sub_log_nat_add_one hs0).sub hh).add hr
  have he (N : ℕ) :
    ∑ n ∈ Finset.range N, digammaLogError s n =
      (Complex.log (s + N) - (Real.log ((N : ℝ) + 1) : ℂ) -
            ((harmonic N : ℂ) - (Real.log ((N : ℝ) + 1) : ℂ)) +
          ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (s + n))) -
        Complex.log s := by
    rw [sum_digammaLogError, Finset.sum_sub_distrib]
    have hhar : ∑ n ∈ Finset.range N, 1 / (n + 1 : ℂ) = (harmonic N : ℂ) := by
      rw [harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, one_div]
    rw [hhar]
    ring
  have hf := hlim.sub_const (Complex.log s)
  simp only [zero_sub, ← digamma_eq_resolventSeries hs0] at hf
  have hg :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, digammaLogError s n) Filter.atTop
      (nhds (Complex.digamma s - Complex.log s)) := by
    simpa only [← he] using hf
  exact tendsto_nhds_unique hg (summable_digammaLogError hs).hasSum.tendsto_sum_nat

/-- The universal real constant given by the sum of 4/(n+1)² over natural indices.
It is finite and independent of the complex argument. It bounds digamma minus log on
Re s ≥ 1/2 and hence controls each gamma factor in analytic conductor comparisons. -/
noncomputable def digammaLogErrorBound : ℝ :=
  ∑' n : ℕ, 4 / ((n : ℝ) + 1) ^ 2

/-- The inverse-square majorant defining the universal digamma error bound is summable.
Shift the convergent reciprocal-square series by one and multiply by four.
This permits comparison of the error-series sum with the universal constant. -/
theorem summable_digammaLogErrorBound : Summable (fun n : ℕ ↦ 4 / ((n : ℝ) + 1) ^ 2) := by
  have h :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (show 1 < (2 : ℕ) by decide))
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h.mul_left 4

/-- On Re s ≥ 1/2, the norm of digamma minus the principal logarithm is bounded by the
universal inverse-square sum. Use the error-series representation and its termwise majorant.
The bound is uniform in all gamma shifts with nonnegative real part at the endpoint one. -/
theorem norm_digamma_sub_log_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ digammaLogErrorBound := by
  rw [digamma_sub_log_eq_tsum_digammaLogError hs]
  exact
    (norm_tsum_le_tsum_norm (summable_digammaLogError hs).norm).trans
      (Summable.tsum_le_tsum (norm_digammaLogError_le hs) (summable_digammaLogError hs).norm
        summable_digammaLogErrorBound)

/-- On Re s ≥ 1/2, the absolute difference between real digamma and log of the argument norm
is bounded by the universal constant. Take real parts of the complex logarithmic estimate.
This is the archimedean estimate used to compare gamma endpoints and analytic conductors. -/
theorem abs_re_digamma_sub_log_norm_le {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    |(Complex.digamma s).re - Real.log ‖s‖| ≤ digammaLogErrorBound := by
  rw [← Complex.log_re, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (norm_digamma_sub_log_le hs)

/-- On the right half-plane with norm at least one, digamma is bounded by the logarithm
of the argument norm plus a universal constant. Bound the principal logarithm using
its real part and the argument bound, then add the uniform digamma error.
This gives logarithmic growth for vertical gamma-factor integrability. -/
theorem norm_digamma_le_log_norm_add {s : ℂ} (hs : 1 / 2 ≤ s.re) (hn : 1 ≤ ‖s‖) :
    ‖Complex.digamma s‖ ≤ Real.log ‖s‖ + Real.pi + digammaLogErrorBound := by
  have hl : ‖Complex.log s‖ ≤ Real.log ‖s‖ + Real.pi := by
    have h := Complex.norm_le_abs_re_add_abs_im (Complex.log s)
    rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hn)] at h
    exact h.trans (add_le_add_right (Complex.abs_arg_le_pi s) _)
  exact
    (norm_le_norm_sub_add _ (Complex.log s)).trans
      ((add_le_add (norm_digamma_sub_log_le hs) hl).trans_eq (by ring))

/-- If the real part of s is at least a fixed positive delta, digamma has a linear
norm bound with inverse-delta loss. Shift by one, use the uniform digamma-log
estimate, and bound the reciprocal by the real part. This supplies growth on
positive strips including half-shifted gamma arguments on the critical line. -/
theorem norm_digamma_le_linear_of_re_ge {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : δ ≤ s.re) :
    ‖Complex.digamma s‖ ≤ ‖s‖ + Real.pi + digammaLogErrorBound + δ⁻¹ := by
  have hp : 0 < s.re := hδ.trans_le hs
  have hn : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m he
    rw [he, Complex.neg_re, Complex.natCast_re] at hp
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg m))) hp
  have hshift : 1 ≤ (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith only [hp]
  have hnorm : 1 ≤ ‖s + 1‖ := hshift.trans (Complex.re_le_norm _)
  have hb := norm_digamma_le_log_norm_add ((by norm_num only : (1 / 2 : ℝ) ≤ 1).trans hshift) hnorm
  have he : Complex.digamma s = Complex.digamma (s + 1) - s⁻¹ := by
    rw [Complex.digamma_apply_add_one s hn, add_sub_cancel_right]
  have hi : ‖s⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact
      (inv_le_inv₀ (hδ.trans_le (hs.trans (Complex.re_le_norm s))) hδ).mpr
        (hs.trans (Complex.re_le_norm s))
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hnorm)
  have ht : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa only [norm_one] using norm_add_le s (1 : ℂ)
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith only [hb, hi, hl, ht])

end PseudoPrime.AnalyticNumberTheory.Gamma
