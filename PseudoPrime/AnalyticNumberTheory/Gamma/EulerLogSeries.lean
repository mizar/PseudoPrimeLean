/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.ResolventSeries
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Euler logarithmic series for gamma and digamma

Summable reciprocal derivative bounds give a holomorphic logarithmic correction series.
Euler's gamma approximations identify its exponential and yield the digamma difference series.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For any natural n and complex s, define (s-1)/(n+1) + log(n+1) - log(s+n), using
principal complex logarithms. It vanishes at s = 1. On Re s > 0 its derivative is
1/(n+1) - 1/(s+n), with an inverse-square majorant on bounded smaller half-planes.
These normalized terms define the convergent Euler logarithm of gamma. -/
noncomputable def logCorrection (n : ℕ) (s : ℂ) : ℂ :=
  (s - 1) / (n + 1) + Complex.log (n + 1) - Complex.log (s + n)

/-- At a point with positive real part, differentiate the pole-free logarithmic correction.
The shifted argument lies in the principal logarithm's slit plane. -/
theorem hasDerivAt_logCorrection (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (logCorrection n) (1 / (n + 1) - 1 / (s + n)) s := by
  have hslit : s + n ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr
      (Or.inl
        (by
          rw [Complex.add_re, Complex.natCast_re]
          exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)))
  have hd := (((hasDerivAt_id s).sub_const 1).div_const (n + 1 : ℂ)).add_const (Complex.log (n + 1))
  have hl := ((hasDerivAt_id s).add_const (n : ℂ)).clog hslit
  convert hd.sub hl using 1 <;> rfl

/-- On a bounded part of Re s > a with 0 < a ≤ 1, the correction derivative has a uniform
inverse-square majorant. Horizontal separation controls the two reciprocal denominators. -/
theorem norm_correctionDerivative_le {a B : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : a < s.re)
    (hB : ‖s‖ < B) (n : ℕ) :
    ‖1 / (n + 1 : ℂ) - 1 / (s + n)‖ ≤ ((B + 1) / a) * (((n : ℝ) + 1) ^ 2)⁻¹ := by
  have hn : (0 : ℝ) < n + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  have hd : a * ((n : ℝ) + 1) ≤ ‖s + n‖ := by
    have hr := Complex.re_le_norm (s + n)
    rw [Complex.add_re, Complex.natCast_re] at hr
    have hm := mul_le_mul_of_nonneg_right ha1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [hr, hs, hm]
  have hz : s + n ≠ 0 := norm_pos_iff.mp ((mul_pos ha hn).trans_le hd)
  have hnz : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have he : 1 / (n + 1 : ℂ) - 1 / (s + n) = (s - 1) / ((n + 1) * (s + n)) := by
    field_simp [hnz, hz]
    ring
  rw [he, norm_div, norm_mul]
  have hnNorm : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      Complex.norm_of_nonneg hn.le]
  rw [hnNorm]
  calc
    ‖s - 1‖ / (((n : ℝ) + 1) * ‖s + n‖) ≤ (B + 1) / (((n : ℝ) + 1) * (a * ((n : ℝ) + 1))) := by
      have hnum : ‖s - 1‖ ≤ B + 1 :=
        (norm_sub_le s (1 : ℂ)).trans
          (by
            rw [norm_one]
            exact add_le_add hB.le le_rfl)
      exact
        div_le_div₀ (add_nonneg ((norm_nonneg s).trans hB.le) zero_le_one) hnum
          (mul_pos hn (mul_pos ha hn)) (mul_le_mul_of_nonneg_left hd hn.le)
    _ = _ := by field_simp [ha.ne', hn.ne']

/-- Every normalized correction vanishes at the anchor point one.
This gives convergence at the base point for differentiating the correction series. -/
theorem logCorrection_one (n : ℕ) : logCorrection n 1 = 0 := by
  unfold logCorrection
  rw [sub_self, zero_div, zero_add, add_comm (1 : ℂ) n, sub_self]

/-- On Re s > 0, the normalized correction series converges and may be differentiated termwise.
Use a convex bounded neighborhood containing one and the summable derivative majorant. -/
theorem logCorrection_summable_and_deriv {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n ↦ logCorrection n s) ∧
      HasDerivAt (fun z ↦ ∑' n : ℕ, logCorrection n z) (∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (s + n)))
        s := by
  obtain ⟨a, ha, ham⟩ := exists_between (lt_min zero_lt_one hs)
  have ha1 : a < 1 := lt_of_lt_of_le ham (min_le_left _ _)
  have has : a < s.re := lt_of_lt_of_le ham (min_le_right _ _)
  let B : ℝ := ‖s‖ + 2
  let U : Set ℂ := {z | a < z.re} ∩ Metric.ball 0 B
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUconvex : Convex ℝ U :=
    (convex_halfSpace_gt ⟨Complex.add_re, Complex.smul_re⟩ a).inter (convex_ball (0 : ℂ) B)
  have h1 : (1 : ℂ) ∈ U := by
    refine ⟨by simpa only [Set.mem_ofPred_eq, Complex.one_re] using ha1, ?_⟩
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    dsimp only [B]
    linarith only [norm_nonneg s]
  have hsU : s ∈ U := by
    refine ⟨has, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [B]
    linarith only
  have hp : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have hh :=
      (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num only : (1 : ℝ) < 2))
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_two] using hh
  have hu := hp.mul_left ((B + 1) / a)
  have hg :
    ∀ (n : ℕ) (z : ℂ), z ∈ U → HasDerivAt (logCorrection n) (1 / (n + 1 : ℂ) - 1 / (z + n)) z :=
    fun n z hz ↦ hasDerivAt_logCorrection n (ha.trans hz.1)
  have hbound :
    ∀ (n : ℕ) (z : ℂ),
      z ∈ U → ‖1 / (n + 1 : ℂ) - 1 / (z + n)‖ ≤ ((B + 1) / a) * (((n : ℝ) + 1) ^ 2)⁻¹ :=
    fun n z hz ↦
    norm_correctionDerivative_le ha ha1.le hz.1
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz.2) n
  have hbase : Summable (fun n ↦ logCorrection n 1) := by
    simpa only [logCorrection_one] using (summable_zero : Summable (fun _ : ℕ ↦ (0 : ℂ)))
  exact
    ⟨summable_of_summable_hasDerivAt_of_isPreconnected hu hUopen hUconvex.isPreconnected hg hbound
        h1 hbase hsU,
      hasDerivAt_tsum_of_isPreconnected hu hUopen hUconvex.isPreconnected hg hbound h1 hbase hsU⟩

/-- For Re s > 0, exponentiation of one correction recovers its rational Euler factor.
Nonzero shifted denominators justify exponentiating the principal logarithms. -/
theorem exp_logCorrection (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Complex.exp (logCorrection n s) = Complex.exp ((s - 1) / (n + 1)) * (n + 1) / (s + n) := by
  have hz : s + n ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hh
    linarith only [hs, hh, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [logCorrection, Complex.exp_sub, Complex.exp_add, Complex.exp_log hz, Complex.exp_log hn]

/-- The exponential of a finite correction sum equals its harmonic exponential times the
factorial divided by the shifted product.
This connects the series to Euler's gamma approximations. -/
theorem exp_sum_logCorrection {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Complex.exp (∑ n ∈ Finset.range N, logCorrection n s) =
      Complex.exp ((s - 1) * (harmonic N : ℂ)) * (N.factorial : ℂ) /
        ∏ n ∈ Finset.range N, (s + n) := by
  rw [Complex.exp_sum]
  simp only [exp_logCorrection _ hs]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hh : (∑ n ∈ Finset.range N, (s - 1) / (n + 1 : ℂ)) = (s - 1) * (harmonic N : ℂ) := by
    rw [harmonic, Rat.cast_sum, Finset.mul_sum]
    exact
      Finset.sum_congr rfl
        (fun n _ ↦ by
          rw [Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, div_eq_mul_inv])
  have hf : (∏ n ∈ Finset.range N, (n + 1 : ℂ)) = (N.factorial : ℂ) := by
    rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun n _ ↦ by rw [Nat.cast_add, Nat.cast_one])
  rw [hh, hf]

/-- For Re s > 0 and positive N, Euler's gamma approximation is an exponential correction sum
with harmonic normalization, times N/(N+1). Finite product identities give the equality. -/
theorem GammaSeq_eq_exp_correction {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : N ≠ 0) :
    Complex.GammaSeq s N =
      Complex.exp
            ((s - 1) * (Complex.log N - (harmonic (N + 1) : ℂ)) +
              ∑ n ∈ Finset.range (N + 1), logCorrection n s) *
          (N : ℂ) /
        (N + 1) := by
  have hz : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hnz : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hprod : (∏ n ∈ Finset.range (N + 1), (s + n)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro n _
    exact (not_neg_nat_of_re_pos hs n) ∘ (eq_neg_of_add_eq_zero_left)
  rw [Complex.exp_add, exp_sum_logCorrection hs, mul_sub, Complex.exp_sub, Complex.GammaSeq,
    Complex.cpow_def_of_ne_zero hz, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hc : Complex.exp ((s - 1) * Complex.log N) = Complex.exp (Complex.log N * s) / (N : ℂ) := by
    rw [sub_mul, one_mul, Complex.exp_sub, Complex.exp_log hz, mul_comm s]
  rw [hc]
  field_simp [hprod, hnz, hz, Complex.exp_ne_zero]

/-- The reciprocal of the successor natural index tends to zero in the real numbers.
Compose reciprocal decay with divergence of natural casts. -/
theorem tendsto_nat_reciprocal_succ :
    Filter.Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun N : ℕ ↦ (N : ℝ)) Filter.atTop Filter.atTop).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ))))

/-- The complex logarithm of N minus the next harmonic number tends to minus Euler's constant.
The extra harmonic reciprocal vanishes in the limit. -/
theorem tendsto_log_sub_harmonic_succ :
    Filter.Tendsto (fun N : ℕ ↦ Complex.log N - (harmonic (N + 1) : ℂ)) Filter.atTop
      (nhds (-(Real.eulerMascheroniConstant : ℂ))) := by
  have h := (Real.tendsto_harmonic_sub_log.add tendsto_nat_reciprocal_succ).neg
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  convert hc using 1
  · funext N
    rw [Function.comp_apply, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one, Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_sub,
      Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Complex.ofReal_log (Nat.cast_nonneg _)]
    simp only [Complex.ofReal_ratCast, Complex.ofReal_natCast]
    ring
  · simp only [add_zero, Complex.ofReal_neg]

/-- For any complex s, define -(s-1) times Euler's constant plus the total sum of
logarithmic corrections. On Re s > 0 the series converges, is holomorphic and has
exponential Gamma(s); no branch or convergence assertion is made outside that half-plane.
Its derivative yields the digamma reciprocal series. -/
noncomputable def logGammaSeries (s : ℂ) : ℂ :=
  -(s - 1) * (Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, logCorrection n s

/-- For Re s > 0, exponentiating the correction series gives the gamma function.
Pass Euler's finite gamma approximation to the limit using harmonic normalization. -/
theorem Gamma_eq_exp_logGammaSeries {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s = Complex.exp (logGammaSeries s) := by
  have hsum :=
    ((logCorrection_summable_and_deriv hs).1.hasSum.tendsto_sum_nat).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hexp := (((tendsto_const_nhds (x := s - 1)).mul tendsto_log_sub_harmonic_succ).add hsum).cexp
  have hfrac : Filter.Tendsto (fun N : ℕ ↦ (N : ℂ) / (N + 1)) Filter.atTop (nhds (1 : ℂ)) := by
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_nat_reciprocal_succ
    have hn := (tendsto_const_nhds (x := (1 : ℂ))).sub hc
    convert hn using 1
    · funext N
      rw [Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one]
      field_simp [show (N + 1 : ℂ) ≠ 0 by exact_mod_cast Nat.succ_ne_zero N]
      ring
    · rw [Complex.ofReal_zero, sub_zero]
  have he := hexp.mul hfrac
  have heq :
    (fun N : ℕ ↦ Complex.GammaSeq s N) =ᶠ[Filter.atTop]
      (fun N ↦
        Complex.exp
            ((s - 1) * (Complex.log N - (harmonic (N + 1) : ℂ)) +
              ∑ n ∈ Finset.range (N + 1), logCorrection n s) *
          ((N : ℂ) / (N + 1))) := by
    filter_upwards [Nat.eventually_pos] with N hN
    rw [GammaSeq_eq_exp_correction hs hN.ne', mul_div_assoc]
  have hlim := he.congr' heq.symm
  have hu := tendsto_nhds_unique (Complex.GammaSeq_tendsto_Gamma s) hlim
  simpa only [mul_one, logGammaSeries, mul_neg, neg_mul] using hu

/-- For Re s > 0, the Euler logarithm of gamma has derivative minus Euler's constant
plus the convergent series 1/(n+1) - 1/(s+n). Differentiate the normalized linear term
and the correction series termwise. This identifies digamma through the exponential
gamma representation. -/
theorem hasDerivAt_logGammaSeries {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt logGammaSeries
      (-(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (s + n))) s := by
  have hd :=
    (((hasDerivAt_id s).sub_const 1).neg.mul_const (Real.eulerMascheroniConstant : ℂ)).add
      (logCorrection_summable_and_deriv hs).2
  convert hd using 1
  · rfl
  · ring

/-- For Re s > 0, digamma equals minus Euler's constant plus the convergent reciprocal series.
Differentiate the exponential gamma representation locally and cancel the nonzero exponential. -/
theorem digamma_eq_resolventSeries {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s =
      -(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (s + n)) := by
  have hd := (hasDerivAt_logGammaSeries hs).cexp
  have he : Complex.Gamma =ᶠ[nhds s] (fun z ↦ Complex.exp (logGammaSeries z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact Gamma_eq_exp_logGammaSeries hz
  have hΓ := hd.congr_of_eventuallyEq he
  rw [Complex.digamma_def, logDeriv_apply, hΓ.deriv, Gamma_eq_exp_logGammaSeries hs]
  exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)

/-- For Re s ≥ 0, the normalized digamma reciprocal difference series is summable.
Apply the inverse-square resolvent bound with the anchor point one. -/
theorem summable_digammaResolvent {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun n : ℕ ↦ (1 / (n + 1 : ℂ) - 1 / (s + n))) := by
  have h := summable_resolventDifference (s := 1) (by norm_num only [Complex.one_re]) hs
  simpa only [add_comm (1 : ℂ)] using h

/-- For two points with positive real parts, the digamma difference is the convergent difference
of shifted reciprocals. Subtract the two normalized series and cancel Euler's constant. -/
theorem digamma_sub_eq_resolventSeries {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    Complex.digamma s - Complex.digamma t = ∑' n : ℕ, (1 / (t + n) - 1 / (s + n)) := by
  rw [digamma_eq_resolventSeries hs, digamma_eq_resolventSeries ht]
  have hh :
    -(Real.eulerMascheroniConstant : ℂ) + (∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (s + n))) -
        (-(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (t + n))) =
      (∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (s + n))) - ∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (t + n)) := by
    ring
  rw [hh, ← (summable_digammaResolvent hs.le).tsum_sub (summable_digammaResolvent ht.le)]
  exact tsum_congr (fun n ↦ by ring)

/-- For two points with positive real parts, their translated digamma difference tends to zero.
The reciprocal series identity identifies the limit of the finite recurrence. -/
theorem tendsto_digamma_sub_add_nat_zero {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    Filter.Tendsto (fun n : ℕ ↦ Complex.digamma (s + n) - Complex.digamma (t + n)) Filter.atTop
      (nhds 0) := by
  have h := tendsto_digamma_sub_add_nat hs ht
  have he :
    Complex.digamma s - Complex.digamma t + (∑' n : ℕ, (1 / (s + n) - 1 / (t + n))) = 0 := by
    rw [digamma_sub_eq_resolventSeries hs ht]
    rw [show (fun n : ℕ ↦ (1 / (t + n) - 1 / (s + n))) = (fun n : ℕ ↦ -(1 / (s + n) - 1 / (t + n)))
        from funext (fun n ↦ by ring),
      tsum_neg, neg_add_cancel]
  exact he ▸ h

end PseudoPrime.AnalyticNumberTheory.Gamma
